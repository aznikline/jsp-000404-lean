import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1800 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h1801 | h1801
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1802 | h1802
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1803 | h1803
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1804 | h1804
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1805 | h1805
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1806 | h1806
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1807 | h1807
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1808 | h1808
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1809 | h1809
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1810 | h1810
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1811 | h1811
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1812 | h1812
                        · linarith only [h0, h1800, h1812, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h1800, h1806, h1809, h1812, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1811, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1810, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1809, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1818 | h1818
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1819 | h1819
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1820 | h1820
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1821 | h1821
                        · linarith only [h0, h1800, h1821, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h1800, h1806, h1821, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1820, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1819, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1818, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1827 | h1827
                · linarith only [h1806, h1807, h1827, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1829 | h1829
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1830 | h1830
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1831 | h1831
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1832 | h1832
                        · linarith only [h0, h1800, h1832, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h1806, h1807, h1829, h1832, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1831, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1830, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1829, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1838 | h1838
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1839 | h1839
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1840 | h1840
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1841 | h1841
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1842 | h1842
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1843 | h1843
                        · linarith only [h1800, h1806, h1843, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1845 | h1845
                          · linarith only [h0, h1801, h1843, h1845, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h1806, h1838, h1840, h1845, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1842, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1841, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1840, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1806, h1838, h1839, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1852 | h1852
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1853 | h1853
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1854 | h1854
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1855 | h1855
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1856 | h1856
                        · linarith only [h1800, h1806, h1856, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1858 | h1858
                          · linarith only [h0, h1800, h1838, h1858, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1860 | h1860
                            · linarith only [h0, h1801, h1860, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h0, h1801, h1852, h1856, h1860, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1855, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1800, h1853, h1854, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1800, h1853, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1866 | h1866
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1867 | h1867
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1868 | h1868
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1869 | h1869
                        · linarith only [h0, h1800, h1869, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1871 | h1871
                          · linarith only [h0, h1801, h1838, h1869, h1871, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1873 | h1873
                            · linarith only [h0, h1801, h1852, h1873, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1875 | h1875
                              · linarith only [h1800, h1806, h1866, h1875, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1877 | h1877
                                · linarith only [h0, h1800, h1838, h1866, h1877, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1879 | h1879
                                  · linarith only [h1804, h1806, h1852, h1879, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1881 | h1881
                                    · rcases h0bigk with h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [hlam, p1882_0]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h0, hlam, p1882_1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h0, h1800, h1866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1882_1, u2elo1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h0, h1800, h1806, h1866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1882_1, u2elo1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h0, h1800, h1806, h1852, h1866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1882_1, u2elo1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p1882_1, u2elo1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [hlam, p1882_0]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        rcases p1882_3 (m.d 0 1) (by simp) with h1890 | h1890
                                        · linarith only [h0, h1890, hlam]
                                        · linarith only [h1800, h1890, hlam]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        rcases p1882_3 (m.d 0 1) (by simp) with h1893 | h1893
                                        · linarith only [h0, h1893, hlam]
                                        · linarith only [h1801, h1893, hlam]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        rcases p1882_3 (m.d 0 1) (by simp) with h1896 | h1896
                                        · linarith only [h0, h1896, hlam]
                                        · linarith only [h1802, h1896, hlam]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h1800, hlam, p1882_1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h1803, hlam, p1882_1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [hlam, p1882_0]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h1806, hlam, p1882_1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h1838, hlam, p1882_1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h1801, hlam, p1882_0]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h1804, hlam, p1882_0]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h1800, h1852, h1866, h1881, hc23, hc34, hlam, hphi, p1882_1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [hlam, p1882_0]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h1852, hlam, p1882_0]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h1802, hlam, p1882_0]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h1805, hlam, p1882_1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h0, h1800, h1802, h1866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1882_1, u2elo1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [h0, h1802, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1882_1, u2elo1]
                                      · have p1882_0 := h1882c.1
                                        have p1882_1 := h1882c.2.1
                                        have p1882_2 := h1882c.2.2.1
                                        have p1882_3 := h1882c.2.2.2
                                        linarith only [hlam, p1882_0]
                                    · rcases h0bigk with h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [hlam, p1914_0]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h0, hlam, p1914_1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h0, h1800, h1866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1914_1, u2elo1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h0, h1801, h1866, h1869, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1914_1, u2elo1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1914_1, u2elo1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p1914_1, u2elo1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [hlam, p1914_0]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        rcases p1914_3 (m.d 0 1) (by simp) with h1922 | h1922
                                        · linarith only [h0, h1922, hlam]
                                        · linarith only [h1800, h1922, hlam]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        rcases p1914_3 (m.d 0 1) (by simp) with h1925 | h1925
                                        · linarith only [h0, h1925, hlam]
                                        · linarith only [h1801, h1925, hlam]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        rcases p1914_3 (m.d 0 1) (by simp) with h1928 | h1928
                                        · linarith only [h0, h1928, hlam]
                                        · linarith only [h1802, h1928, hlam]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h1800, hlam, p1914_1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h1803, hlam, p1914_1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [hlam, p1914_0]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h1806, hlam, p1914_1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h1838, hlam, p1914_1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h1801, hlam, p1914_0]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h1804, hlam, p1914_0]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h0, h1800, h1801, h1866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1914_1, u2elo1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [hlam, p1914_0]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h1852, hlam, p1914_0]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h1802, hlam, p1914_0]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h1805, hlam, p1914_1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h0, h1800, h1802, h1866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1914_1, u2elo1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [h0, h1802, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1914_1, u2elo1]
                                      · have p1914_0 := h1914c.1
                                        have p1914_1 := h1914c.2.1
                                        have p1914_2 := h1914c.2.2.1
                                        have p1914_3 := h1914c.2.2.2
                                        linarith only [hlam, p1914_0]
                      · linarith only [h0, h1868, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1800, h1804, h1866, h1867, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1800, h1866, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h1802, h1805, hlam]
        · linarith only [h0, h1801, h1804, hlam]
      · linarith only [h0, h1800, h1803, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1952 | h1952
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1953 | h1953
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1954 | h1954
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1955 | h1955
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1956 | h1956
              · linarith only [h1800, h1802, h1956, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1958 | h1958
                · linarith only [h1800, h1802, h1955, h1958, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1960 | h1960
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1961 | h1961
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1962 | h1962
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1963 | h1963
                        · linarith only [h1800, h1802, h1962, h1963, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h1800, h1802, h1955, h1960, h1962, h1963, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1954, h1962, hc12, hlam, hphi, u2elo0]
                    · linarith only [h0, h1800, h1960, h1961, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1960, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1969 | h1969
              · linarith only [h1801, h1802, h1955, h1969, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1971 | h1971
                · linarith only [h1801, h1802, h1971, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1973 | h1973
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1974 | h1974
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1975 | h1975
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1976 | h1976
                        · linarith only [h1800, h1955, h1976, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1978 | h1978
                          · linarith only [h1800, h1802, h1969, h1975, h1978, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1980 | h1980
                            · linarith only [h1801, h1802, h1975, h1980, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1982 | h1982
                              · linarith only [h0, h1952, h1955, h1982, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1984 | h1984
                                · linarith only [h1800, h1801, h1802, h1973, h1978, h1984, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1986 | h1986
                                  · linarith only [h1801, h1802, h1974, h1980, h1986, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1988 | h1988
                                    · linarith only [h1801, h1802, h1973, h1976, h1980, h1988, hc23, hc34, hlam, hphi]
                                    · rcases h0bigk with h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c | h1990c
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [hlam, p1990_0]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h0, hlam, p1990_1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1802, h1978, hc03, hc35, hlam, hphi, p1990_1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1802, h1975, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1990_1, u2elo1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1802, hlam, p1990_1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p1990_1, u2elo1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [hlam, p1990_0]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        rcases p1990_3 (m.d 0 1) (by simp) with h1998 | h1998
                                        · linarith only [h0, h1998, hlam]
                                        · linarith only [h1800, h1998, hlam]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        rcases p1990_3 (m.d 0 1) (by simp) with h2001 | h2001
                                        · linarith only [h0, h2001, hlam]
                                        · linarith only [h1801, h2001, hlam]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h0, h1801, h1802, h1973, h1976, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1990_1, u2elo1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1800, hlam, p1990_1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1952, hlam, p1990_1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [hlam, p1990_0]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1955, hlam, p1990_1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1969, hlam, p1990_1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1801, hlam, p1990_0]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1953, hlam, p1990_0]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h0, h1800, h1801, h1973, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1990_1, u2elo1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [hlam, p1990_0]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1971, hlam, p1990_0]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1800, h1973, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1990_1, u0elo4]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [h1954, hlam, p1990_1]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        rcases p1990_3 (m.d 0 1) (by simp) with h2017 | h2017
                                        · linarith only [h1802, h2017, hlam]
                                        · linarith only [h1800, h2017, hlam]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        rcases p1990_3 (m.d 0 1) (by simp) with h2020 | h2020
                                        · linarith only [h1802, h2020, hlam]
                                        · linarith only [h1801, h2020, hlam]
                                      · have p1990_0 := h1990c.1
                                        have p1990_1 := h1990c.2.1
                                        have p1990_2 := h1990c.2.2.1
                                        have p1990_3 := h1990c.2.2.2
                                        linarith only [hlam, p1990_0]
                      · linarith only [h0, h1954, h1975, hlam]
                    · linarith only [h0, h1974, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1973, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2027 | h2027
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2028 | h2028
              · linarith only [h1800, h1802, h2028, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2030 | h2030
                · linarith only [h0, h1801, h1954, h2030, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2032 | h2032
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2033 | h2033
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2034 | h2034
                      · linarith only [h0, h1954, h2034, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1800, h2032, h2034, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1800, h2032, h2033, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2032, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2039 | h2039
              · linarith only [h0, h1801, h1954, h2027, h2039, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2041 | h2041
                · linarith only [h0, h1801, h1954, h2041, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2043 | h2043
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2044 | h2044
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2045 | h2045
                      · linarith only [h0, h1954, h2045, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1800, h2043, h2045, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1800, h2043, h2044, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1800, h2043, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h1801, h1953, hlam]
      · linarith only [h0, h1800, h1952, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2052 | h2052
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2053 | h2053
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2054 | h2054
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2055 | h2055
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2056 | h2056
            · linarith only [h1800, h1801, h2056, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2058 | h2058
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2059 | h2059
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2060 | h2060
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2061 | h2061
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2062 | h2062
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2063 | h2063
                        · linarith only [h1800, h2056, h2063, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2065 | h2065
                          · linarith only [h1800, h1801, h2061, h2065, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h1800, h1801, h2058, h2060, h2061, h2065, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1801, h2061, h2062, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h2054, h2061, hlam]
                  · linarith only [h0, h1800, h2058, h2060, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h1800, h1801, h2058, h2059, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2072 | h2072
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2073 | h2073
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2074 | h2074
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2075 | h2075
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2076 | h2076
                        · linarith only [h0, h1800, h2076, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2078 | h2078
                          · linarith only [h1800, h1801, h2058, h2074, h2078, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2080 | h2080
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2081 | h2081
                              · linarith only [h1801, h2052, h2073, h2076, h2078, h2081, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2083 | h2083
                                · linarith only [h1800, h2058, h2073, h2083, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2085 | h2085
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2086 | h2086
                                    · rcases h0bigk with h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h0, hlam, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h1801, h2074, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2087_1, u2elo1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h1801, hlam, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h1801, h2074, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2087_1, u2elo1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2087_1, u2elo1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        rcases p2087_3 (m.d 0 1) (by simp) with h2095 | h2095
                                        · linarith only [h0, h2095, hlam]
                                        · linarith only [h1800, h2095, hlam]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h0, h1801, h2052, h2073, h2078, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2087_1, u2elo1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        rcases p2087_3 (m.d 0 1) (by simp) with h2099 | h2099
                                        · linarith only [h0, h2099, hlam]
                                        · linarith only [h2052, h2099, hlam]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h1800, hlam, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2053, hlam, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2056, hlam, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2058, hlam, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2052, h2073, h2078, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2087_1, u0elo3]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2054, hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        rcases p2087_3 (m.d 0 1) (by simp) with h2109 | h2109
                                        · linarith only [h1801, h2109, hlam]
                                        · linarith only [h1800, h2109, hlam]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        rcases p2087_3 (m.d 0 1) (by simp) with h2113 | h2113
                                        · linarith only [h1801, h2113, hlam]
                                        · linarith only [h2052, h2113, hlam]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2052, hlam, p2087_0]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2055, hlam, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h0, h1800, h2052, h2073, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2087_1, u2elo1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [h2072, hlam, p2087_1]
                                      · have p2087_0 := h2087c.1
                                        have p2087_1 := h2087c.2.1
                                        have p2087_2 := h2087c.2.2.1
                                        have p2087_3 := h2087c.2.2.2
                                        linarith only [hlam, p2087_0]
                                    · linarith only [h1800, h1801, h2073, h2076, h2086, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h0, h2052, h2080, h2085, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h1801, h2052, h2073, h2078, h2080, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h1801, h2074, h2075, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h2052, h2074, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h1800, h2073, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h1801, h2052, h2072, hlam]
          · linarith only [h1801, h2052, h2054, h2055, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2129 | h2129
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2130 | h2130
            · linarith only [h0, h1800, h2054, h2130, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2132 | h2132
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2133 | h2133
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2134 | h2134
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2135 | h2135
                    · linarith only [h0, h2054, h2135, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1800, h2134, h2135, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2134, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h0, h1800, h2054, h2132, h2133, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2140 | h2140
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2141 | h2141
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2142 | h2142
                    · linarith only [h0, h1800, h2054, h2141, h2142, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1800, h2141, h2142, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2141, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h0, h2052, h2054, h2140, hlam]
          · linarith only [h0, h2052, h2129, hlam]
      · linarith only [h0, h1800, h2053, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2149 | h2149
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2150 | h2150
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2151 | h2151
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2152 | h2152
            · linarith only [h1800, h1801, h2152, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2154 | h2154
              · linarith only [h1800, h2052, h2154, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2156 | h2156
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2157 | h2157
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2158 | h2158
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2159 | h2159
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2160 | h2160
                        · linarith only [h1800, h2152, h2160, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2162 | h2162
                          · linarith only [h1800, h1801, h2154, h2158, h2162, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2164 | h2164
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2165 | h2165
                              · linarith only [h2052, h2160, h2164, h2165, hc01, hlam, hphi, ht12, u2elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2167 | h2167
                                · linarith only [h1800, h2052, h2157, h2162, h2167, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2169 | h2169
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2170 | h2170
                                    · rcases h0bigk with h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c | h2171c
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [hlam, p2171_0]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h0, hlam, p2171_1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h1800, h2052, h2157, h2160, h2164, hc23, hc34, hlam, hphi, p2171_1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h1801, hlam, p2171_1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h2052, hlam, p2171_1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2171_1, u2elo1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [hlam, p2171_0]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        rcases p2171_3 (m.d 0 1) (by simp) with h2179 | h2179
                                        · linarith only [h0, h2179, hlam]
                                        · linarith only [h1800, h2179, hlam]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h0, h1800, h1801, h2157, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2171_1, u2elo1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h0, h1800, h2052, h2157, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2171_1, u2elo1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h1800, hlam, p2171_1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h2149, hlam, p2171_1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [hlam, p2171_0]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h2152, hlam, p2171_1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h2154, hlam, p2171_1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h1800, h2157, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2171_1, u0elo3]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h2150, hlam, p2171_0]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        rcases p2171_3 (m.d 0 1) (by simp) with h2191 | h2191
                                        · linarith only [h1801, h2191, hlam]
                                        · linarith only [h1800, h2191, hlam]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [hlam, p2171_0]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h1800, h1801, h2052, h2157, h2158, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2171_1, u2elo1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h1800, h2157, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2171_1, u0elo4]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h2151, hlam, p2171_1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        rcases p2171_3 (m.d 0 1) (by simp) with h2198 | h2198
                                        · linarith only [h2052, h2198, hlam]
                                        · linarith only [h1800, h2198, hlam]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [h2156, hlam, p2171_1]
                                      · have p2171_0 := h2171c.1
                                        have p2171_1 := h2171c.2.1
                                        have p2171_2 := h2171c.2.2.1
                                        have p2171_3 := h2171c.2.2.2
                                        linarith only [hlam, p2171_0]
                                    · linarith only [h0, h2150, h2169, h2170, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2204 | h2204
                                    · rcases h0bigk with h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [hlam, p2205_0]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h0, hlam, p2205_1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h0, h1800, h2157, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2205_1, u2elo1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h1801, hlam, p2205_1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h2052, hlam, p2205_1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2205_1, u2elo1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [hlam, p2205_0]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        rcases p2205_3 (m.d 0 1) (by simp) with h2213 | h2213
                                        · linarith only [h0, h2213, hlam]
                                        · linarith only [h1800, h2213, hlam]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h0, h2156, h2169, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2205_1, u2elo1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h0, h1800, h2052, h2157, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2205_1, u2elo1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h1800, hlam, p2205_1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h2149, hlam, p2205_1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [hlam, p2205_0]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h2152, hlam, p2205_1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h2154, hlam, p2205_1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h1800, h2157, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2205_1, u0elo3]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h2150, hlam, p2205_0]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        rcases p2205_3 (m.d 0 1) (by simp) with h2225 | h2225
                                        · linarith only [h1801, h2225, hlam]
                                        · linarith only [h1800, h2225, hlam]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [hlam, p2205_0]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h1800, h1801, h2052, h2157, h2158, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2205_1, u2elo1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h1800, h2157, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2205_1, u0elo4]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h2151, hlam, p2205_1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        rcases p2205_3 (m.d 0 1) (by simp) with h2232 | h2232
                                        · linarith only [h2052, h2232, hlam]
                                        · linarith only [h1800, h2232, hlam]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [h2156, hlam, p2205_1]
                                      · have p2205_0 := h2205c.1
                                        have p2205_1 := h2205c.2.1
                                        have p2205_2 := h2205c.2.2.1
                                        have p2205_3 := h2205c.2.2.2
                                        linarith only [hlam, p2205_0]
                                    · linarith only [h1800, h1801, h2157, h2160, h2204, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h1801, h2156, h2164, hlam]
                      · linarith only [h0, h2151, h2159, hlam]
                    · linarith only [h0, h1800, h2157, h2158, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1800, h2157, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2242 | h2242
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2243 | h2243
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2244 | h2244
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2245 | h2245
                        · linarith only [h1800, h1801, h2243, h2245, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2247 | h2247
                          · linarith only [h1800, h1801, h2243, h2247, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2249 | h2249
                            · linarith only [h1800, h1801, h2156, h2242, h2243, h2249, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h1800, h1801, h2242, h2249, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h2151, h2244, hlam]
                    · linarith only [h0, h1800, h2242, h2243, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1800, h2242, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2255 | h2255
            · linarith only [h1800, h1801, h2255, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2257 | h2257
              · linarith only [h0, h1800, h2151, h2257, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2259 | h2259
                · linarith only [h2150, h2151, h2259, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2261 | h2261
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2262 | h2262
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2263 | h2263
                      · linarith only [h1801, h2150, h2151, h2263, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1800, h2261, h2263, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1800, h2261, h2262, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2261, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2268 | h2268
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2269 | h2269
            · linarith only [h0, h1800, h2150, h2269, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2271 | h2271
              · linarith only [h1800, h2052, h2271, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2273 | h2273
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2274 | h2274
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2275 | h2275
                    · linarith only [h1800, h2052, h2150, h2268, h2274, h2275, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1800, h2274, h2275, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2274, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2150, h2268, h2273, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2280 | h2280
            · linarith only [h0, h1800, h2150, h2280, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2282 | h2282
              · linarith only [h0, h1800, h2268, h2282, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2284 | h2284
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2285 | h2285
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2286 | h2286
                    · linarith only [h0, h1800, h2150, h2285, h2286, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1800, h2285, h2286, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2285, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2290 | h2290
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2291 | h2291
                    · linarith only [h0, h1800, h2150, h2290, h2291, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1800, h2290, h2291, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1800, h2290, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h1800, h2149, hlam]

end R2N4
