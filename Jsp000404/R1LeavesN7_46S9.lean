import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6014000 in
set_option maxHeartbeats 6014000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h966 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1840 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1841 | h1841
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1842 | h1842
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1843 | h1843
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1844 | h1844
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1845 | h1845
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1846 | h1846
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1847 | h1847
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1848 | h1848
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1849 | h1849
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1850 | h1850
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1851 | h1851
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1852 | h1852
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1853 | h1853
                          · linarith only [h1840, h1853, h966, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1840, h1847, h1849, h1853, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h1852, h966, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h1840, h1845, h1851, h966, hlam]
                    · linarith only [h0, h1844, h1850, hlam]
                  · linarith only [h0, h1843, h1849, hlam]
                · linarith only [h0, h1842, h1848, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1861 | h1861
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1862 | h1862
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1863 | h1863
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1864 | h1864
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1865 | h1865
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1866 | h1866
                          · linarith only [h1840, h1847, h1866, h966, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1868 | h1868
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1869 | h1869
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1870 | h1870
                                · linarith only [h1840, h1847, h1862, h1870, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1872 | h1872
                                  · linarith only [h1840, h1847, h1862, h1868, h1872, hlam]
                                  · rcases h0bigk with h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h0, hlam, p1874_1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h966, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h966, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1874_1, u3elo1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h966, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1874_1, u3elo1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1841, hc15, hlam, hphi, ht0b, ht5b, p1874_1, u0elo1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1840, h1862, h1868, h966, hc34, hlam, hphi, ht0b, ht45, ht5b, p1874_1, u0elo1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      rcases p1874_3 (m.d 0 1) (by simp) with h1883 | h1883
                                      · linarith only [h0, h1883, hlam]
                                      · linarith only [h1840, h1883, hlam]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      rcases p1874_3 (m.d 0 1) (by simp) with h1886 | h1886
                                      · linarith only [h0, h1886, hlam]
                                      · linarith only [h1841, h1886, hlam]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1841, h1862, h1866, h1868, hc34, hlam, hphi, ht0b, ht45, ht5b, p1874_1, u0elo2]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1842, hlam, p1874_1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      rcases p1874_3 (m.d 0 1) (by simp) with h1892 | h1892
                                      · linarith only [h1892, h966, hlam]
                                      · linarith only [h1840, h1892, hlam]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      rcases p1874_3 (m.d 0 1) (by simp) with h1895 | h1895
                                      · linarith only [h1895, h966, hlam]
                                      · linarith only [h1841, h1895, hlam]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1840, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1843, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1845, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1847, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1841, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1844, hlam, p1874_1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1846, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1840, h1841, h1862, h1868, h966, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1874_1, u3elo1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [hlam, p1874_0]
                              · linarith only [h1846, h1869, h966, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1845, h1868, h966, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1865, h966, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h1841, h1845, h1864, h966, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                    · linarith only [h0, h1844, h1863, hlam]
                  · linarith only [h0, h1843, h1862, hlam]
                · linarith only [h0, h1861, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h1841, h1846, h966, hlam]
          · linarith only [h1840, h1845, h966, hlam]
        · linarith only [h0, h1841, h1844, hlam]
      · linarith only [h1840, h1842, h1843, h966, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1919 | h1919
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1920 | h1920
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1921 | h1921
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1922 | h1922
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1923 | h1923
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1924 | h1924
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1925 | h1925
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1926 | h1926
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1927 | h1927
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1928 | h1928
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1929 | h1929
                          · linarith only [h0, h1840, h1842, h1924, h1929, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h0, h1840, h1842, h1923, h1924, h1925, h1929, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h0, h1842, h1924, h1928, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1840, h1842, h1921, h1924, h1927, hlam]
                    · linarith only [h1842, h1920, h1924, h1926, hc12, hlam, hphi, ht23, u3elo1]
                  · linarith only [h0, h1842, h1924, h1925, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h1924, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1937 | h1937
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1938 | h1938
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1939 | h1939
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1940 | h1940
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1941 | h1941
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1942 | h1942
                          · linarith only [h1840, h1923, h1942, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1944 | h1944
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1945 | h1945
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1946 | h1946
                                · linarith only [h1840, h1923, h1938, h1946, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1948 | h1948
                                  · linarith only [h1840, h1923, h1938, h1944, h1948, hlam]
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
                                      linarith only [h0, hlam, p1950_1]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h966, hlam, p1950_0]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1840, h1938, h1944, h966, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1950_1, u3elo1]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h966, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1950_1, u3elo1]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1840, h1938, h1944, hc34, hlam, hphi, ht0b, ht45, ht5b, p1950_1, u0elo1]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [hlam, p1950_0]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1842, hlam, p1950_0]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1840, h1842, h1937, h1938, h1944, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1950_1, u3elo1]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1841, h1842, h1937, h1938, h1942, h1944, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1950_1, u3elo1]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1841, h1842, h1937, h1938, h1942, h1944, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1950_1, u3elo1]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1842, h1937, hc02, hlam, hphi, ht23, p1950_1, u3elo1]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [hlam, p1950_0]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      rcases p1950_3 (m.d 0 1) (by simp) with h1964 | h1964
                                      · linarith only [h1964, h966, hlam]
                                      · linarith only [h1840, h1964, hlam]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      rcases p1950_3 (m.d 0 1) (by simp) with h1967 | h1967
                                      · linarith only [h1967, h966, hlam]
                                      · linarith only [h1841, h1967, hlam]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1840, hlam, p1950_0]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1919, hlam, p1950_0]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1921, hlam, p1950_0]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [hlam, p1950_0]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1923, hlam, p1950_0]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1841, hlam, p1950_0]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1920, hlam, p1950_1]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1922, hlam, p1950_0]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [h1840, h1841, h1938, h1944, h966, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1950_1, u3elo1]
                                    · have p1950_0 := h1950c.1
                                      have p1950_1 := h1950c.2.1
                                      have p1950_2 := h1950c.2.2.1
                                      have p1950_3 := h1950c.2.2.2
                                      linarith only [hlam, p1950_0]
                              · linarith only [h0, h1842, h1945, hc01, hlam, hphi, ht12, ht23, u3elo4]
                            · linarith only [h0, h1841, h1842, h1938, h1942, h1944, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h1941, h966, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1842, h1937, h1940, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h1840, h1842, h1937, h1938, h1939, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1842, h1937, h1938, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h1840, h1937, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h1841, h1922, h966, hlam]
          · linarith only [h0, h1840, h1842, h1921, hlam]
        · linarith only [h0, h1841, h1920, hlam]
      · linarith only [h0, h1840, h1919, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1991 | h1991
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1992 | h1992
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1993 | h1993
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1994 | h1994
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1995 | h1995
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1996 | h1996
              · linarith only [h1840, h1841, h1996, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1998 | h1998
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1999 | h1999
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2000 | h2000
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2001 | h2001
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2002 | h2002
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2003 | h2003
                          · linarith only [h1840, h1996, h2003, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2005 | h2005
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2006 | h2006
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2007 | h2007
                                · linarith only [h1841, h1992, h2003, h2007, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2009 | h2009
                                  · linarith only [h1840, h1841, h1999, h2003, h2005, h2009, hlam]
                                  · rcases h0bigk with h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [hlam, p2011_0]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h0, hlam, p2011_1]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h966, hlam, p2011_0]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1840, h1841, h1999, h2002, h2005, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2011_1, u3elo1]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1841, hlam, p2011_1]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1840, h1999, h2005, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1, u0elo1]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [hlam, p2011_0]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1840, h1999, h2005, h966, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1, u0elo1]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      rcases p2011_3 (m.d 0 1) (by simp) with h2020 | h2020
                                      · linarith only [h0, h2020, hlam]
                                      · linarith only [h1840, h2020, hlam]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1840, h1841, h1999, h2005, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1, u0elo1]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1840, h1999, h2005, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1, u0elo2]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1991, hlam, p2011_1]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [hlam, p2011_0]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      rcases p2011_3 (m.d 0 1) (by simp) with h2027 | h2027
                                      · linarith only [h2027, h966, hlam]
                                      · linarith only [h1840, h2027, hlam]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1840, h1841, h1999, h2005, h966, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2011_1, u3elo1]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1840, hlam, p2011_0]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1992, hlam, p2011_0]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1994, hlam, p2011_0]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [hlam, p2011_0]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1996, hlam, p2011_0]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1840, h1999, h2005, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1, u0elo4]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1993, hlam, p2011_1]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [h1995, hlam, p2011_0]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      rcases p2011_3 (m.d 0 1) (by simp) with h2039 | h2039
                                      · linarith only [h1841, h2039, hlam]
                                      · linarith only [h1840, h2039, hlam]
                                    · have p2011_0 := h2011c.1
                                      have p2011_1 := h2011c.2.1
                                      have p2011_2 := h2011c.2.2.1
                                      have p2011_3 := h2011c.2.2.2
                                      linarith only [hlam, p2011_0]
                              · linarith only [h1995, h2006, h966, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1994, h2005, h966, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1995, h2002, h966, hlam]
                      · linarith only [h2001, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h1993, h2000, hlam]
                  · linarith only [h0, h1992, h1999, hlam]
                · linarith only [h0, h1998, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2050 | h2050
              · linarith only [h1840, h1841, h2050, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2052 | h2052
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2053 | h2053
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2054 | h2054
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2055 | h2055
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2056 | h2056
                        · linarith only [h1995, h2056, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1840, h2053, h2056, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h1840, h2053, h2055, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h1993, h2054, hlam]
                  · linarith only [h0, h1992, h2053, hlam]
                · linarith only [h0, h1991, h2052, hlam]
          · linarith only [h1840, h1994, h966, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2064 | h2064
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2065 | h2065
            · linarith only [h1991, h1993, h2065, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2067 | h2067
              · linarith only [h1840, h1991, h1993, h2067, h966, hc23, hlam, hphi, u3elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2069 | h2069
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2070 | h2070
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2071 | h2071
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2072 | h2072
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2073 | h2073
                        · linarith only [h1840, h2065, h2070, h2073, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h1840, h2070, h2073, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h1840, h2070, h2072, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2077 | h2077
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2078 | h2078
                        · linarith only [h1840, h2065, h2070, h2078, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h1840, h2070, h2078, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h1840, h2070, h2077, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h0, h1992, h2070, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h1991, h2069, hlam]
          · linarith only [h1840, h2064, h966, hlam]
      · linarith only [h0, h1840, h1992, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2086 | h2086
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2087 | h2087
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2088 | h2088
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2089 | h2089
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2090 | h2090
              · linarith only [h1840, h1841, h2090, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2092 | h2092
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2093 | h2093
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2094 | h2094
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2095 | h2095
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2096 | h2096
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2097 | h2097
                          · linarith only [h1840, h1841, h1991, h2087, h2090, h2092, h2097, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2099 | h2099
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2100 | h2100
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2101 | h2101
                                · linarith only [h1840, h1841, h1991, h2087, h2092, h2093, h2097, h2101, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2103 | h2103
                                  · linarith only [h1840, h1841, h2093, h2097, h2099, h2103, hlam]
                                  · rcases h0bigk with h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h0, hlam, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h966, hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1841, h1991, h2087, h2092, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2105_1, u3elo1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1841, hlam, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1991, h2092, hc01, hlam, hphi, ht12, ht23, p2105_1, u3elo1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1991, hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1840, h1991, h2092, h2093, h2099, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2105_1, u3elo1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1991, h2092, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2105_1, u3elo1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1840, h2093, h2099, hc34, hlam, hphi, ht0b, ht45, ht5b, p2105_1, u0elo2]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1991, h2092, hc02, hlam, hphi, ht23, p2105_1, u3elo1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      rcases p2105_3 (m.d 0 1) (by simp) with h2119 | h2119
                                      · linarith only [h2119, h966, hlam]
                                      · linarith only [h1840, h2119, hlam]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1840, h1841, h1991, h2092, h2093, h2099, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2105_1, u3elo1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1840, hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2086, hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2088, hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2090, hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1840, h2087, h2093, h2099, hc34, hlam, hphi, ht0b, ht45, ht5b, p2105_1, u0elo1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2087, hlam, p2105_1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h2089, hlam, p2105_0]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [h1840, h1991, h2087, h2092, h2093, h2099, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2105_1, u3elo1]
                                    · have p2105_0 := h2105c.1
                                      have p2105_1 := h2105c.2.1
                                      have p2105_2 := h2105c.2.2.1
                                      have p2105_3 := h2105c.2.2.2
                                      linarith only [hlam, p2105_0]
                              · linarith only [h1991, h2100, hc02, hlam, hphi, ht23, u3elo4]
                            · linarith only [h1840, h1841, h1991, h2087, h2093, h2099, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h1991, h2087, h2089, h2096, hc13, hlam, hphi, u3elo2]
                      · linarith only [h1840, h1841, h1991, h2087, h2088, h2092, h2093, h2095, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h1840, h1841, h1991, h2087, h2092, h2093, h2094, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h1840, h1841, h1991, h2087, h2092, h2093, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1840, h2092, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h1991, h2087, h2089, hlam]
          · linarith only [h0, h1840, h1991, h2088, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2142 | h2142
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2143 | h2143
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2144 | h2144
              · linarith only [h0, h1840, h2087, h2144, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2146 | h2146
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2147 | h2147
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2148 | h2148
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2149 | h2149
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2150 | h2150
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2151 | h2151
                          · linarith only [h1840, h2144, h2151, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2153 | h2153
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2154 | h2154
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2155 | h2155
                                · linarith only [h2086, h2087, h2148, h2151, h2155, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2157 | h2157
                                  · linarith only [h0, h2087, h2148, h2151, h2157, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                  · rcases h0bigk with h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h0, hlam, p2159_1]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h966, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h0, h1840, h2087, h2147, h2148, h2151, h2153, hc34, hc45, hlam, hphi, p2159_1]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1841, hlam, p2159_1]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h2087, h2148, h2150, hc01, hc13, hlam, hphi, p2159_1]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1991, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1840, h1991, h2147, h2153, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2159_1, u3elo2]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h2087, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h966, hc01, hlam, hphi, ht12, ht23, p2159_1, u3elo1]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h966, hc02, hlam, hphi, ht23, p2159_1, u3elo1]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      rcases p2159_3 (m.d 0 1) (by simp) with h2173 | h2173
                                      · linarith only [h2173, h966, hlam]
                                      · linarith only [h1840, h2173, hlam]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1840, h1841, h1991, h2146, h2147, h2153, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2159_1, u3elo1]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1840, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h2086, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h2142, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h2144, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1840, h2147, h2153, hc34, hlam, hphi, ht0b, ht45, ht5b, p2159_1, u0elo4]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h0, h1840, h2087, h2147, h2148, h2150, h2153, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2159_1, u3elo1]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h2143, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      rcases p2159_3 (m.d 0 1) (by simp) with h2185 | h2185
                                      · linarith only [h1841, h2185, hlam]
                                      · linarith only [h1840, h2185, hlam]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [hlam, p2159_0]
                              · linarith only [h1991, h2143, h2154, hlam]
                            · linarith only [h1991, h2153, hc02, hlam, hphi, ht23, u3elo3]
                        · linarith only [h1840, h2147, h2150, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h1840, h1991, h2146, h2147, h2149, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h1840, h1991, h2146, h2147, h2148, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1991, h2146, h2147, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h1840, h2146, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2196 | h2196
              · linarith only [h1840, h1841, h2196, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2198 | h2198
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2199 | h2199
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2200 | h2200
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2201 | h2201
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2202 | h2202
                        · linarith only [h2143, h2202, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1840, h2199, h2202, h966, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h1840, h1991, h2198, h2199, h2201, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h1840, h1991, h2198, h2199, h2200, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1840, h1991, h2198, h2199, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1840, h2198, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · linarith only [h0, h1840, h1991, h2142, hlam]
      · linarith only [h0, h1840, h2086, hlam]

end R2N4
