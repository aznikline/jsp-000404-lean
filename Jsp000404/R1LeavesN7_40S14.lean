import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6854000 in
set_option maxHeartbeats 6854000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1838 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1839 | h1839
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1840 | h1840
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1841 | h1841
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1842 | h1842
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1843 | h1843
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1844 | h1844
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1845 | h1845
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1846 | h1846
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1847 | h1847
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1848 | h1848
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1849 | h1849
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1850 | h1850
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1851 | h1851
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1852 | h1852
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1853 | h1853
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1854 | h1854
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1855 | h1855
                                  · linarith only [h1840, h1852, h1855, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h1845, h1855, hc34, hlam, hphi, u4elo0]
                                · linarith only [h1314, h1838, h1840, h1851, h1854, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h1314, h1838, h1840, h1850, h1851, h1852, h1853, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1860 | h1860
                              · linarith only [h1843, h1852, h1860, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1862 | h1862
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1863 | h1863
                                  · rcases h0bigk with h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [hlam, p1864_0]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h0, hlam, p1864_1]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1314, hlam, p1864_0]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1838, h1850, h1851, h1860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1, u0elo0]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1314, h1839, h1846, h1850, h1860, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1864_1]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1838, h1850, h1851, h1860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1, u0elo1]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [hlam, p1864_0]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1314, h1838, h1850, h1851, h1860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1, u0elo1]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1838, h1850, h1851, h1860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1, u0elo1]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1839, h1850, h1860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1, u0elo1]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1838, h1850, h1851, h1860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1, u0elo2]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1840, hlam, p1864_1]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [hlam, p1864_0]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1838, h1840, h1850, h1851, h1860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1, u0elo1]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1839, h1840, h1850, h1860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1, u0elo1]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1838, hlam, p1864_0]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1841, hlam, p1864_0]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1843, hlam, p1864_0]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [hlam, p1864_0]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1839, h1850, h1860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1, u0elo3]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1839, hlam, p1864_0]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1842, hlam, p1864_1]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1844, hlam, p1864_0]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [h1845, hlam, p1864_1]
                                    · have p1864_0 := h1864c.1
                                      have p1864_1 := h1864c.2.1
                                      have p1864_2 := h1864c.2.2.1
                                      have p1864_3 := h1864c.2.2.2
                                      linarith only [hlam, p1864_0]
                                  · linarith only [h1862, h1863, hc34, hlam, hphi, u4elo2]
                                · linarith only [h1838, h1851, h1862, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1845, h1851, hc14, hlam, hphi, u4elo0]
                        · linarith only [h1314, h1844, h1850, hlam]
                      · linarith only [h1314, h1849, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h1838, h1842, h1847, h1848, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · linarith only [h0, h1847, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1840, h1846, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1898 | h1898
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1899 | h1899
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1900 | h1900
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1901 | h1901
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1902 | h1902
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1903 | h1903
                          · linarith only [h1838, h1845, h1903, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1905 | h1905
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1906 | h1906
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1907 | h1907
                                · linarith only [h1838, h1845, h1899, h1907, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1909 | h1909
                                  · linarith only [h1840, h1845, h1905, h1909, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases h0bigk with h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [hlam, p1911_0]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h0, hlam, p1911_1]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1314, hlam, p1911_0]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      rcases p1911_3 (m.d 0 1) (by simp) with h1915 | h1915
                                      · rcases p1911_3 (m.d 0 2) (by simp) with h1916 | h1916
                                        · rcases p1911_3 (m.d 0 3) (by simp) with h1917 | h1917
                                          · rcases p1911_3 (m.d 0 4) (by simp) with h1918 | h1918
                                            · linarith only [h1838, h1918, hlam]
                                            · rcases p1911_3 (m.d 0 5) (by simp) with h1920 | h1920
                                              · linarith only [h1839, h1920, hlam]
                                              · linarith only [h1845, h1920, hlam]
                                          · linarith only [h1843, h1917, hlam]
                                        · linarith only [h1841, h1916, hlam]
                                      · linarith only [h1838, h1915, hlam]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      rcases p1911_3 (m.d 0 1) (by simp) with h1926 | h1926
                                      · rcases p1911_3 (m.d 0 2) (by simp) with h1927 | h1927
                                        · rcases p1911_3 (m.d 0 3) (by simp) with h1928 | h1928
                                          · rcases p1911_3 (m.d 0 4) (by simp) with h1929 | h1929
                                            · linarith only [h1838, h1929, hlam]
                                            · rcases p1911_3 (m.d 0 5) (by simp) with h1931 | h1931
                                              · linarith only [h1839, h1931, hlam]
                                              · rcases h0emin with h1933 | h1933 | h1933 | h1933 | h1933
                                                · rcases h1bigk with h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c | h1934c
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h0, hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1314, hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    rcases p1934_3 (m.d 0 1) (by simp) with h1938 | h1938
                                                    · rcases p1934_3 (m.d 1 2) (by simp) with h1939 | h1939
                                                      · rcases p1934_3 (m.d 1 3) (by simp) with h1940 | h1940
                                                        · rcases p1934_3 (m.d 1 4) (by simp) with h1941 | h1941
                                                          · linarith only [h1941, hlam, p1934_0]
                                                          · rcases p1934_3 (m.d 1 5) (by simp) with h1943 | h1943
                                                            · linarith only [h1839, h1943, hlam]
                                                            · linarith only [h1903, h1943, hlam]
                                                        · linarith only [h1901, h1940, hlam]
                                                      · linarith only [h1899, h1939, hlam]
                                                    · linarith only [h1938, hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    rcases p1934_3 (m.d 0 1) (by simp) with h1949 | h1949
                                                    · rcases p1934_3 (m.d 1 2) (by simp) with h1950 | h1950
                                                      · rcases p1934_3 (m.d 1 3) (by simp) with h1951 | h1951
                                                        · rcases p1934_3 (m.d 1 4) (by simp) with h1952 | h1952
                                                          · linarith only [h1838, h1952, hlam]
                                                          · rcases p1934_3 (m.d 1 5) (by simp) with h1954 | h1954
                                                            · linarith only [h1954, hlam, p1934_0]
                                                            · rcases h3bigk with h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c | h1956c
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1314, hlam, p1956_1]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1840, h1905, hc34, hlam, hphi, ht0b, ht45, ht5b, p1956_1, u0elo1]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                rcases p1956_3 (m.d 0 3) (by simp) with h1960 | h1960
                                                                · rcases p1956_3 (m.d 1 3) (by simp) with h1961 | h1961
                                                                  · rcases p1956_3 (m.d 2 3) (by simp) with h1962 | h1962
                                                                    · linarith only [h1840, h1962, hlam]
                                                                    · linarith only [h1905, h1962, hlam]
                                                                  · linarith only [h1901, h1961, hlam]
                                                                · linarith only [h1960, hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                rcases p1956_3 (m.d 0 3) (by simp) with h1967 | h1967
                                                                · rcases p1956_3 (m.d 1 3) (by simp) with h1968 | h1968
                                                                  · rcases p1956_3 (m.d 2 3) (by simp) with h1969 | h1969
                                                                    · linarith only [h1840, h1969, hlam]
                                                                    · linarith only [h1906, h1969, hlam]
                                                                  · linarith only [h1902, h1968, hlam]
                                                                · linarith only [h1967, hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1314, h1898, h1933, hc12, hlam, ht01, p1956_1]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                rcases p1956_3 (m.d 0 3) (by simp) with h1976 | h1976
                                                                · linarith only [h1314, h1976, hlam]
                                                                · linarith only [h1840, h1976, hlam]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1314, h1839, h1899, h1903, h1905, hlam, p1911_1, p1956_2]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1314, h1844, hlam, p1911_1, p1956_2]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1840, hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1898, hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1840, hc34, hlam, hphi, ht0b, ht45, ht5b, p1956_1, u0elo1]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1840, hc35, hlam, hphi, ht0b, ht5b, p1956_1, u0elo1]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1843, hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1901, hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1905, hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1909, hlam, p1956_1]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1844, hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1902, hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1906, hlam, p1956_0]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [h1844, hc34, hlam, hphi, ht0b, ht45, ht5b, p1956_1, u0elo2]
                                                              · have p1956_0 := h1956c.1
                                                                have p1956_1 := h1956c.2.1
                                                                have p1956_2 := h1956c.2.2.1
                                                                have p1956_3 := h1956c.2.2.2
                                                                linarith only [hlam, p1956_0]
                                                        · linarith only [h1902, h1951, hlam]
                                                      · linarith only [h1900, h1950, hlam]
                                                    · linarith only [h1949, hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1839, h1899, h1903, h1905, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1911_1, p1934_1]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1314, h1839, h1899, h1903, h1905, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1911_1, p1934_1]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h0, h1839, h1903, hlam, p1911_1, p1934_2]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1314, h1839, h1898, hlam, p1911_1, p1934_2]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1839, h1898, h1899, h1903, h1905, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1911_1, p1934_1]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1898, hlam, p1934_1]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1314, h1839, h1903, hlam, p1911_1, p1934_2]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1314, h1839, hlam, p1911_1, p1934_2]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1838, hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1899, hlam, p1934_1]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1901, hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1903, hlam, p1934_1]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1839, hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1900, hlam, p1934_1]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1902, hlam, p1934_0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [h1839, h1899, h1905, hc34, hlam, hphi, ht0b, ht45, ht5b, p1911_1, p1934_1, u0elo0]
                                                  · have p1934_0 := h1934c.1
                                                    have p1934_1 := h1934c.2.1
                                                    have p1934_2 := h1934c.2.2.1
                                                    have p1934_3 := h1934c.2.2.2
                                                    linarith only [hlam, p1934_0]
                                                · rcases h1bigk with h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c
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
                                                    linarith only [h1314, hlam, p2019_0]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    rcases p2019_3 (m.d 0 1) (by simp) with h2023 | h2023
                                                    · rcases p2019_3 (m.d 1 2) (by simp) with h2024 | h2024
                                                      · rcases p2019_3 (m.d 1 3) (by simp) with h2025 | h2025
                                                        · rcases p2019_3 (m.d 1 4) (by simp) with h2026 | h2026
                                                          · linarith only [h2026, hlam, p2019_0]
                                                          · rcases p2019_3 (m.d 1 5) (by simp) with h2028 | h2028
                                                            · linarith only [h1839, h2028, hlam]
                                                            · linarith only [h1903, h2028, hlam]
                                                        · linarith only [h1901, h2025, hlam]
                                                      · linarith only [h1899, h2024, hlam]
                                                    · linarith only [h2023, hlam, p2019_0]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    rcases p2019_3 (m.d 0 1) (by simp) with h2034 | h2034
                                                    · rcases p2019_3 (m.d 1 2) (by simp) with h2035 | h2035
                                                      · rcases p2019_3 (m.d 1 3) (by simp) with h2036 | h2036
                                                        · rcases p2019_3 (m.d 1 4) (by simp) with h2037 | h2037
                                                          · linarith only [h1838, h2037, hlam]
                                                          · rcases p2019_3 (m.d 1 5) (by simp) with h2039 | h2039
                                                            · linarith only [h2039, hlam, p2019_0]
                                                            · rcases h3bigk with h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c | h2041c
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1314, hlam, p2041_1]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1840, h1905, hc34, hlam, hphi, ht0b, ht45, ht5b, p2041_1, u0elo1]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                rcases p2041_3 (m.d 0 3) (by simp) with h2045 | h2045
                                                                · rcases p2041_3 (m.d 1 3) (by simp) with h2046 | h2046
                                                                  · rcases p2041_3 (m.d 2 3) (by simp) with h2047 | h2047
                                                                    · linarith only [h1840, h2047, hlam]
                                                                    · linarith only [h1905, h2047, hlam]
                                                                  · linarith only [h1901, h2046, hlam]
                                                                · linarith only [h2045, hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                rcases p2041_3 (m.d 0 3) (by simp) with h2052 | h2052
                                                                · rcases p2041_3 (m.d 1 3) (by simp) with h2053 | h2053
                                                                  · rcases p2041_3 (m.d 2 3) (by simp) with h2054 | h2054
                                                                    · linarith only [h1840, h2054, hlam]
                                                                    · linarith only [h1906, h2054, hlam]
                                                                  · linarith only [h1902, h2053, hlam]
                                                                · linarith only [h2052, hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1314, h1898, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1911_1, p2041_1]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                rcases p2041_3 (m.d 0 3) (by simp) with h2061 | h2061
                                                                · linarith only [h1314, h2061, hlam]
                                                                · linarith only [h1840, h2061, hlam]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1314, h1838, h1845, h1899, h1905, hlam, p1911_1, p2041_2]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1314, h1842, h1906, hlam, p1911_1, p2041_2]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1840, hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1898, hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1840, hc34, hlam, hphi, ht0b, ht45, ht5b, p2041_1, u0elo1]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1840, hc35, hlam, hphi, ht0b, ht5b, p2041_1, u0elo1]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1843, hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1901, hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1905, hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1909, hlam, p2041_1]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1844, hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1902, hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1906, hlam, p2041_0]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [h1844, hc34, hlam, hphi, ht0b, ht45, ht5b, p2041_1, u0elo2]
                                                              · have p2041_0 := h2041c.1
                                                                have p2041_1 := h2041c.2.1
                                                                have p2041_2 := h2041c.2.2.1
                                                                have p2041_3 := h2041c.2.2.2
                                                                linarith only [hlam, p2041_0]
                                                        · linarith only [h1902, h2036, hlam]
                                                      · linarith only [h1900, h2035, hlam]
                                                    · linarith only [h2034, hlam, p2019_0]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1838, h1845, h1899, h1905, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1911_1, p2019_1]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [hlam, p2019_0]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1314, h1838, h1845, h1899, h1905, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1911_1, p2019_1]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h0, h1838, h1845, hlam, p1911_1, p2019_2]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1314, h1839, h1898, hlam, p1911_1, p2019_2]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1838, h1845, h1898, h1899, h1905, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1911_1, p2019_1]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1898, hlam, p2019_1]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [hlam, p2019_0]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1314, h1838, h1845, hlam, p1911_1, p2019_2]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1314, h1839, hlam, p1911_1, p2019_2]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1838, hlam, p2019_0]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1899, hlam, p2019_1]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1901, hlam, p2019_0]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [hlam, p2019_0]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1903, hlam, p2019_1]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1839, hlam, p2019_0]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1900, hlam, p2019_1]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1902, hlam, p2019_0]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [h1839, h1899, h1905, hc34, hlam, hphi, ht0b, ht45, ht5b, p1911_1, p2019_1, u0elo0]
                                                  · have p2019_0 := h2019c.1
                                                    have p2019_1 := h2019c.2.1
                                                    have p2019_2 := h2019c.2.2.1
                                                    have p2019_3 := h2019c.2.2.2
                                                    linarith only [hlam, p2019_0]
                                                · rcases h1bigk with h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h0, hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1314, hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    rcases p2104_3 (m.d 0 1) (by simp) with h2108 | h2108
                                                    · rcases p2104_3 (m.d 1 2) (by simp) with h2109 | h2109
                                                      · rcases p2104_3 (m.d 1 3) (by simp) with h2110 | h2110
                                                        · rcases p2104_3 (m.d 1 4) (by simp) with h2111 | h2111
                                                          · linarith only [h2111, hlam, p2104_0]
                                                          · rcases p2104_3 (m.d 1 5) (by simp) with h2113 | h2113
                                                            · linarith only [h1839, h2113, hlam]
                                                            · linarith only [h1903, h2113, hlam]
                                                        · linarith only [h1901, h2110, hlam]
                                                      · linarith only [h1899, h2109, hlam]
                                                    · linarith only [h2108, hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    rcases p2104_3 (m.d 0 1) (by simp) with h2119 | h2119
                                                    · rcases p2104_3 (m.d 1 2) (by simp) with h2120 | h2120
                                                      · rcases p2104_3 (m.d 1 3) (by simp) with h2121 | h2121
                                                        · rcases p2104_3 (m.d 1 4) (by simp) with h2122 | h2122
                                                          · linarith only [h1838, h2122, hlam]
                                                          · rcases p2104_3 (m.d 1 5) (by simp) with h2124 | h2124
                                                            · linarith only [h2124, hlam, p2104_0]
                                                            · rcases h3bigk with h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1314, hlam, p2126_1]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1840, h1905, hc34, hlam, hphi, ht0b, ht45, ht5b, p2126_1, u0elo1]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                rcases p2126_3 (m.d 0 3) (by simp) with h2130 | h2130
                                                                · rcases p2126_3 (m.d 1 3) (by simp) with h2131 | h2131
                                                                  · rcases p2126_3 (m.d 2 3) (by simp) with h2132 | h2132
                                                                    · linarith only [h1840, h2132, hlam]
                                                                    · linarith only [h1905, h2132, hlam]
                                                                  · linarith only [h1901, h2131, hlam]
                                                                · linarith only [h2130, hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                rcases p2126_3 (m.d 0 3) (by simp) with h2137 | h2137
                                                                · rcases p2126_3 (m.d 1 3) (by simp) with h2138 | h2138
                                                                  · rcases p2126_3 (m.d 2 3) (by simp) with h2139 | h2139
                                                                    · linarith only [h1840, h2139, hlam]
                                                                    · linarith only [h1906, h2139, hlam]
                                                                  · linarith only [h1902, h2138, hlam]
                                                                · linarith only [h2137, hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1898, h1933, hc12, hlam, ht01, p2126_1]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                rcases p2126_3 (m.d 0 3) (by simp) with h2146 | h2146
                                                                · linarith only [h1314, h2146, hlam]
                                                                · linarith only [h1840, h2146, hlam]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1314, h1838, h1845, h1899, h1905, hlam, p1911_1, p2126_2]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1314, h1844, hlam, p1911_1, p2126_2]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1840, hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1898, hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1840, hc34, hlam, hphi, ht0b, ht45, ht5b, p2126_1, u0elo1]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1840, hc35, hlam, hphi, ht0b, ht5b, p2126_1, u0elo1]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1843, hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1901, hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1905, hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1909, hlam, p2126_1]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1844, hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1902, hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1906, hlam, p2126_0]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [h1844, hc34, hlam, hphi, ht0b, ht45, ht5b, p2126_1, u0elo2]
                                                              · have p2126_0 := h2126c.1
                                                                have p2126_1 := h2126c.2.1
                                                                have p2126_2 := h2126c.2.2.1
                                                                have p2126_3 := h2126c.2.2.2
                                                                linarith only [hlam, p2126_0]
                                                        · linarith only [h1902, h2121, hlam]
                                                      · linarith only [h1900, h2120, hlam]
                                                    · linarith only [h2119, hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1838, h1845, h1899, h1905, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1911_1, p2104_1]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1314, h1838, h1845, h1899, h1905, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1911_1, p2104_1]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h0, h1838, h1845, hlam, p1911_1, p2104_2]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1314, h1839, h1898, hlam, p1911_1, p2104_2]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1838, h1845, h1898, h1899, h1905, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1911_1, p2104_1]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1898, hlam, p2104_1]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1314, h1838, h1845, hlam, p1911_1, p2104_2]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1314, h1839, hlam, p1911_1, p2104_2]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1838, hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1899, hlam, p2104_1]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1901, hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1903, hlam, p2104_1]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1839, hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1900, hlam, p2104_1]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1902, hlam, p2104_0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [h1839, h1899, h1905, hc34, hlam, hphi, ht0b, ht45, ht5b, p1911_1, p2104_1, u0elo0]
                                                  · have p2104_0 := h2104c.1
                                                    have p2104_1 := h2104c.2.1
                                                    have p2104_2 := h2104c.2.2.1
                                                    have p2104_3 := h2104c.2.2.2
                                                    linarith only [hlam, p2104_0]
                                                · linarith only [h1845, h1933, hlam, ht01, ht12, ht23, ht34, u4elo4]
                                                · linarith only [h1314, h1933, hc13, hlam, ht01, p1911_1]
                                          · linarith only [h1844, h1928, hlam]
                                        · linarith only [h1842, h1927, hlam]
                                      · linarith only [h1839, h1926, hlam]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1838, h1899, h1905, hc34, hlam, hphi, ht0b, ht45, ht5b, p1911_1, u0elo1]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [hlam, p1911_0]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1314, h1838, h1899, h1905, hc34, hlam, hphi, ht0b, ht45, ht5b, p1911_1, u0elo1]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      rcases p1911_3 (m.d 0 1) (by simp) with h2197 | h2197
                                      · linarith only [h0, h2197, hlam]
                                      · linarith only [h1838, h2197, hlam]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      rcases p1911_3 (m.d 0 1) (by simp) with h2200 | h2200
                                      · linarith only [h0, h2200, hlam]
                                      · linarith only [h1839, h2200, hlam]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1839, h1900, h1905, h1907, hc34, hlam, hphi, ht0b, ht45, ht5b, p1911_1, u0elo2]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1840, hlam, p1911_1]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [hlam, p1911_0]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      rcases p1911_3 (m.d 0 1) (by simp) with h2206 | h2206
                                      · linarith only [h1314, h2206, hlam]
                                      · linarith only [h1838, h2206, hlam]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      rcases p1911_3 (m.d 0 1) (by simp) with h2209 | h2209
                                      · linarith only [h1314, h2209, hlam]
                                      · linarith only [h1839, h2209, hlam]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1838, hlam, p1911_0]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1841, hlam, p1911_0]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1843, hlam, p1911_0]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [hlam, p1911_0]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1845, hlam, p1911_0]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1839, hlam, p1911_0]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1842, hlam, p1911_1]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1844, hlam, p1911_0]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [h1838, h1845, h1899, h1905, hc34, hlam, hphi, p1911_1, u4elo4]
                                    · have p1911_0 := h1911c.1
                                      have p1911_1 := h1911c.2.1
                                      have p1911_2 := h1911c.2.2.1
                                      have p1911_3 := h1911c.2.2.2
                                      linarith only [hlam, p1911_0]
                              · linarith only [h1839, h1902, h1905, h1906, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1843, h1845, h1905, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h1314, h1844, h1902, hlam]
                      · linarith only [h1314, h1901, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h1842, h1900, hlam]
                  · linarith only [h1314, h1898, h1899, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1838, h1840, h1898, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h1314, h1839, h1844, hlam]
          · linarith only [h1314, h1838, h1843, hc14, hlam, hphi, u4elo3]
        · linarith only [h0, h1839, h1842, hlam]
      · linarith only [h1840, h1841, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2233 | h2233
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2234 | h2234
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2235 | h2235
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2236 | h2236
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2237 | h2237
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2238 | h2238
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2239 | h2239
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2240 | h2240
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2241 | h2241
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2242 | h2242
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2243 | h2243
                          · linarith only [h0, h1838, h1840, h2238, h2243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h2237, h2243, hc14, hlam, hphi, u4elo0]
                        · linarith only [h0, h1838, h1840, h2236, h2238, h2239, h2242, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1314, h1838, h2239, h2241, hc24, hlam, hphi, u4elo3]
                    · linarith only [h1840, h2234, h2240, hc12, hc23, hlam, hphi]
                  · linarith only [h1840, h2238, h2239, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2250 | h2250
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2251 | h2251
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2252 | h2252
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2253 | h2253
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2254 | h2254
                          · linarith only [h0, h1838, h2238, h2254, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h1838, h2237, h2238, h2254, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h1314, h2236, h2253, hlam]
                      · linarith only [h1314, h2252, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2234, h2251, hlam]
                  · linarith only [h0, h2250, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2261 | h2261
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2262 | h2262
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2263 | h2263
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2264 | h2264
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2265 | h2265
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2266 | h2266
                          · linarith only [h1838, h2237, h2266, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2268 | h2268
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2269 | h2269
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2270 | h2270
                                · linarith only [h0, h1839, h1840, h2237, h2261, h2262, h2266, h2270, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2272 | h2272
                                  · linarith only [h1838, h2237, h2262, h2268, h2272, hlam]
                                  · rcases h0bigk with h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h0, hlam, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1314, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h0, h1840, h2261, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h0, h1840, h2261, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1840, h2261, hc01, hc12, hlam, hphi, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1840, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1838, h1840, h2261, h2262, h2268, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1839, h1840, h2261, h2263, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1838, h1840, h2261, h2262, h2268, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h0, h1838, h1840, h2261, h2262, h2268, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      rcases p2274_3 (m.d 0 1) (by simp) with h2288 | h2288
                                      · linarith only [h1314, h2288, hlam]
                                      · linarith only [h1838, h2288, hlam]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      rcases p2274_3 (m.d 0 1) (by simp) with h2291 | h2291
                                      · linarith only [h1314, h2291, hlam]
                                      · linarith only [h1839, h2291, hlam]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1838, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h2233, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h2235, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h2237, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1839, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h2234, hlam, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h2236, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h0, h1838, h1839, h1840, h2261, h2262, h2268, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [hlam, p2274_0]
                              · linarith only [h1840, h2236, h2269, hlam]
                            · linarith only [h0, h1840, h2268, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                        · linarith only [h0, h1839, h1840, h2236, h2261, h2265, hlam]
                      · linarith only [h0, h1838, h1840, h2261, h2262, h2264, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h1838, h1840, h2261, h2262, h2263, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1838, h1840, h2261, h2262, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2310 | h2310
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2311 | h2311
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2312 | h2312
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2313 | h2313
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2314 | h2314
                          · linarith only [h1838, h2237, h2314, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2316 | h2316
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2317 | h2317
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2318 | h2318
                                · linarith only [h1838, h2237, h2310, h2318, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2320 | h2320
                                  · linarith only [h1838, h2237, h2310, h2316, h2320, hlam]
                                  · rcases h0bigk with h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h0, hlam, p2322_1]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h1314, hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h0, h1838, h2261, h2310, h2316, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2322_1]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h0, h2261, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2322_1]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h0, h2261, hc01, hc23, hlam, hphi, ht12, p2322_1]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h1840, hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      rcases p2322_3 (m.d 0 1) (by simp) with h2331 | h2331
                                      · linarith only [h0, h2331, hlam]
                                      · linarith only [h1838, h2331, hlam]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      rcases p2322_3 (m.d 0 1) (by simp) with h2334 | h2334
                                      · linarith only [h0, h2334, hlam]
                                      · linarith only [h1839, h2334, hlam]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h1839, h2310, h2314, h2316, hc34, hlam, hphi, ht0b, ht45, ht5b, p2322_1, u0elo2]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h0, h1839, h2310, h2314, h2316, hc34, hlam, hphi, ht0b, ht45, ht5b, p2322_1, u0elo2]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      rcases p2322_3 (m.d 0 1) (by simp) with h2340 | h2340
                                      · linarith only [h1314, h2340, hlam]
                                      · linarith only [h1838, h2340, hlam]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      rcases p2322_3 (m.d 0 1) (by simp) with h2343 | h2343
                                      · linarith only [h1314, h2343, hlam]
                                      · linarith only [h1839, h2343, hlam]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h1838, hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h2233, hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h2235, hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h2237, hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h1839, hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h2234, hlam, p2322_1]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h2236, hlam, p2322_0]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [h0, h1838, h1839, h2261, h2310, h2316, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2322_1]
                                    · have p2322_0 := h2322c.1
                                      have p2322_1 := h2322c.2.1
                                      have p2322_2 := h2322c.2.2.1
                                      have p2322_3 := h2322c.2.2.2
                                      linarith only [hlam, p2322_0]
                              · linarith only [h0, h2261, h2317, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h1314, h1839, h2261, h2310, h2314, h2316, hc24, hlam, hphi, u4elo3]
                        · linarith only [h1314, h2236, h2313, hlam]
                      · linarith only [h1314, h2312, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h1838, h2234, h2310, h2311, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1838, h2310, hc14, hlam, hphi, u4elo2]
            · linarith only [h1314, h1839, h2236, hlam]
          · linarith only [h0, h1838, h1840, h2235, hc14, hlam, hphi, u4elo3]
        · linarith only [h0, h1839, h2234, hlam]
      · linarith only [h0, h1838, h2233, hc14, hlam, hphi, u4elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2366 | h2366
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2367 | h2367
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2368 | h2368
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2369 | h2369
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2370 | h2370
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2371 | h2371
              · linarith only [h1838, h1839, h2371, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2373 | h2373
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2374 | h2374
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2375 | h2375
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2376 | h2376
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2377 | h2377
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2378 | h2378
                          · linarith only [h1838, h2371, h2378, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1838, h1839, h2378, hc14, hlam, hphi, u4elo4]
                        · linarith only [h1314, h1838, h2366, h2370, h2374, h2377, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h1314, h1838, h2374, h2376, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h1838, h2368, h2370, h2374, h2375, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h2366, h2374, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h0, h1838, h2366, h2373, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2386 | h2386
              · linarith only [h1314, h1838, h2370, h2386, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2388 | h2388
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2389 | h2389
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2390 | h2390
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2391 | h2391
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2392 | h2392
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2393 | h2393
                          · linarith only [h1838, h2386, h2393, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1314, h1838, h2370, h2389, h2392, h2393, hc24, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2396 | h2396
                          · linarith only [h1314, h1838, h2392, h2396, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1314, h1838, h2389, h2392, h2396, hc24, hlam, hphi, u4elo4]
                      · linarith only [h1314, h1838, h2389, h2391, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h1838, h2368, h2389, h2390, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1838, h2389, hc14, hlam, hphi, u4elo2]
                · linarith only [h0, h2366, h2388, hlam]
          · linarith only [h1314, h1838, h2369, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2404 | h2404
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2405 | h2405
            · linarith only [h2366, h2368, h2405, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2407 | h2407
              · linarith only [h1314, h1838, h2366, h2368, h2407, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2409 | h2409
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2410 | h2410
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2411 | h2411
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2412 | h2412
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2413 | h2413
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2414 | h2414
                          · linarith only [h1838, h2407, h2414, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1314, h1838, h2366, h2368, h2411, h2414, hc14, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2417 | h2417
                          · linarith only [h1314, h1838, h2366, h2368, h2411, h2417, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h1314, h1838, h2366, h2368, h2411, h2417, hc14, hlam, hphi, u4elo4]
                      · linarith only [h1314, h1838, h2410, h2412, hc24, hlam, hphi, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2421 | h2421
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2422 | h2422
                        · linarith only [h1314, h1838, h2405, h2409, h2410, h2411, h2422, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2424 | h2424
                          · linarith only [h0, h1838, h2411, h2424, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h1838, h2410, h2411, h2424, hc24, hlam, hphi, u4elo4]
                      · linarith only [h1314, h1838, h2410, h2421, hc24, hlam, hphi, u4elo3]
                  · linarith only [h1314, h1838, h2409, h2410, hc14, hlam, hphi, u4elo2]
                · linarith only [h0, h1838, h2366, h2409, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
          · linarith only [h1314, h1838, h2404, hc14, hlam, hphi, u4elo3]
      · linarith only [h2366, h2367, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2432 | h2432
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2433 | h2433
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2434 | h2434
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2435 | h2435
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2436 | h2436
              · linarith only [h1838, h1839, h2436, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2438 | h2438
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2439 | h2439
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2440 | h2440
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2441 | h2441
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2442 | h2442
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2443 | h2443
                          · linarith only [h1838, h2436, h2443, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1838, h1839, h2443, hc14, hlam, hphi, u4elo4]
                        · linarith only [h2366, h2433, h2435, h2438, h2442, hlam]
                      · linarith only [h1838, h1839, h2366, h2433, h2438, h2441, hc14, hlam, hphi, u4elo3]
                    · linarith only [h2366, h2433, h2438, h2440, hlam]
                  · linarith only [h1838, h1839, h2366, h2433, h2438, h2439, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2450 | h2450
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2451 | h2451
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2452 | h2452
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2453 | h2453
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2454 | h2454
                          · linarith only [h1838, h1839, h2438, h2451, h2454, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h1838, h1839, h2454, hc14, hlam, hphi, u4elo4]
                        · linarith only [h1314, h1838, h2433, h2435, h2450, h2453, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1314, h1838, h2366, h2450, h2452, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h1838, h2366, h2433, h2450, h2451, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1838, h2450, hc14, hlam, hphi, u4elo2]
            · linarith only [h2366, h2433, h2435, hlam]
          · linarith only [h0, h1838, h2366, h2434, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2463 | h2463
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2464 | h2464
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2465 | h2465
              · linarith only [h0, h1838, h2433, h2465, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2467 | h2467
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2468 | h2468
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2469 | h2469
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2470 | h2470
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2471 | h2471
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2472 | h2472
                          · linarith only [h1838, h2465, h2472, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h1838, h2433, h2469, h2472, hc14, hlam, hphi, u4elo4]
                        · linarith only [h1314, h1838, h2464, h2468, h2471, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1314, h1838, h2468, h2470, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h1838, h2366, h2467, h2468, h2469, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h2366, h2467, h2468, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2479 | h2479
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2480 | h2480
                    · linarith only [h0, h1838, h2433, h2467, h2479, h2480, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2482 | h2482
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2483 | h2483
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2484 | h2484
                          · linarith only [h0, h1838, h2467, h2484, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h1838, h2480, h2484, hc14, hlam, hphi, u4elo4]
                        · linarith only [h1314, h1838, h2464, h2479, h2483, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h0, h1838, h2467, h2479, h2482, hc24, hlam, hphi, u4elo3]
                  · linarith only [h0, h1838, h2479, hc14, hlam, hphi, u4elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2490 | h2490
              · linarith only [h1314, h1838, h2464, h2490, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2492 | h2492
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2493 | h2493
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2494 | h2494
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2495 | h2495
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2496 | h2496
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2497 | h2497
                          · linarith only [h1838, h2490, h2497, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1838, h1839, h2493, h2497, hc24, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2500 | h2500
                          · linarith only [h1838, h2490, h2500, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h1838, h2366, h2492, h2496, h2500, hc14, hlam, hphi, u4elo4]
                      · linarith only [h0, h1838, h2366, h2492, h2493, h2495, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h1838, h2366, h2492, h2493, h2494, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1838, h2366, h2492, h2493, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2506 | h2506
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2507 | h2507
                    · linarith only [h0, h1838, h2433, h2492, h2506, h2507, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2509 | h2509
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2510 | h2510
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2511 | h2511
                          · linarith only [h0, h1838, h2366, h2464, h2510, h2511, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h1838, h2366, h2464, h2510, h2511, hc14, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2514 | h2514
                          · linarith only [h0, h1838, h2492, h2510, h2514, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1838, h1839, h2506, h2514, hc24, hlam, hphi, u4elo4]
                      · linarith only [h0, h1838, h2492, h2506, h2509, hc24, hlam, hphi, u4elo3]
                  · linarith only [h0, h1838, h2506, hc14, hlam, hphi, u4elo2]
          · linarith only [h0, h1838, h2366, h2463, hc14, hlam, hphi, u4elo3]
      · linarith only [h0, h1838, h2432, hc14, hlam, hphi, u4elo2]

end R2N4
