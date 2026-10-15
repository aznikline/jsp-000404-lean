import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_33S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1852 | h1852
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1853 | h1853
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1854 | h1854
      · linarith only [h0, h1, h1854, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1856 | h1856
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1857 | h1857
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1858 | h1858
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1859 | h1859
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1860 | h1860
                · linarith only [h0, h1854, h1857, h1860, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1862 | h1862
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1863 | h1863
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1864 | h1864
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1865 | h1865
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1866 | h1866
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1867 | h1867
                            · linarith only [h0, h1, h1860, h1862, h1867, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1, h1860, h1867, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h1852, h1859, h1864, h1866, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1, h1862, h1864, h1865, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h1, h1864, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h1856, h1862, h1863, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1874 | h1874
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1875 | h1875
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1876 | h1876
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1877 | h1877
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1878 | h1878
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1879 | h1879
                              · linarith only [h0, h1, h1860, h1874, h1879, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h1, h1852, h1853, h1860, h1862, h1874, h1876, h1879, hc05, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1, h1852, h1860, h1875, h1878, hlam]
                          · linarith only [h1, h1852, h1859, h1860, h1862, h1874, h1876, h1877, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h0, h1, h1874, h1876, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1, h1852, h1857, h1875, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h1, h1856, h1860, h1874, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1887 | h1887
                · linarith only [h0, h1, h1854, h1887, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1889 | h1889
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1890 | h1890
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1891 | h1891
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1892 | h1892
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1893 | h1893
                          · linarith only [h0, h1, h1859, h1887, h1889, h1893, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1895 | h1895
                            · linarith only [h0, h1, h1887, h1889, h1895, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1, h1887, h1895, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1, h1889, h1891, h1892, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h1, h1890, h1891, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h1, h1856, h1889, h1890, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1901 | h1901
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1902 | h1902
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1903 | h1903
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1904 | h1904
                          · linarith only [h1852, h1859, h1904, hlam]
                          · linarith only [h1889, h1901, h1904, hlam]
                        · linarith only [h1, h1852, h1889, h1903, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h1852, h1889, h1902, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h1856, h1887, h1901, hc12, hc23, hlam, hphi]
            · linarith only [h1857, h1858, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1, h1852, h1857, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1912 | h1912
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1913 | h1913
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1914 | h1914
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1915 | h1915
                · linarith only [h0, h1, h1854, h1915, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1917 | h1917
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1918 | h1918
                    · linarith only [h0, h1, h1856, h1915, h1918, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1920 | h1920
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1921 | h1921
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1922 | h1922
                          · linarith only [h1917, h1918, h1922, hlam]
                          · linarith only [h1, h1852, h1914, h1915, h1920, h1922, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1, h1921, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h1853, h1912, h1917, h1918, h1920, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1927 | h1927
                    · linarith only [h0, h1856, h1927, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1929 | h1929
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1930 | h1930
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1931 | h1931
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1932 | h1932
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1933 | h1933
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1934 | h1934
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1935 | h1935
                                  · rcases h1bigk with h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1, h1915, hc12, hc23, hlam, hphi, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1, h1929, h1935, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1, h1930, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1936_1, u3ehi4]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h0, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1915, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1917, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1927, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1852, h1929, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1936_1, u3ehi3]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      rcases p1936_3 (m.d 0 1) (by simp) with h1948 | h1948
                                      · linarith only [h1, h1948, hlam]
                                      · linarith only [h0, h1948, hlam]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      rcases p1936_3 (m.d 0 1) (by simp) with h1952 | h1952
                                      · linarith only [h1, h1952, hlam]
                                      · linarith only [h1852, h1952, hlam]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      rcases p1936_3 (m.d 0 1) (by simp) with h1955 | h1955
                                      · linarith only [h1, h1955, hlam]
                                      · linarith only [h1853, h1955, hlam]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1852, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1, h1852, h1915, hc12, hc23, hlam, hphi, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1929, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1, h1852, h1915, h1930, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1936_1, u3ehi4]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1853, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1, h1853, h1915, hc12, hc23, hlam, hphi, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1930, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1931, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                  · linarith only [h1, h1852, h1914, h1915, h1935, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1, h1852, h1915, h1931, h1934, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h1, h1852, h1915, h1931, h1933, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h1852, h1915, h1929, h1932, hlam]
                          · linarith only [h1, h1852, h1914, h1915, h1929, h1931, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1, h1930, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h1852, h1912, h1929, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1975 | h1975
                · linarith only [h0, h1, h1975, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1977 | h1977
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1978 | h1978
                    · linarith only [h0, h1856, h1978, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1980 | h1980
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1981 | h1981
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1982 | h1982
                          · linarith only [h0, h1, h1914, h1975, h1977, h1982, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1984 | h1984
                            · linarith only [h1, h1853, h1975, h1977, h1978, h1984, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1, h1852, h1853, h1975, h1977, h1978, h1980, h1984, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h1, h1853, h1977, h1978, h1980, h1981, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1, h1853, h1977, h1978, h1980, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1989 | h1989
                    · linarith only [h0, h1856, h1989, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1991 | h1991
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1992 | h1992
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1993 | h1993
                          · linarith only [h1852, h1914, h1993, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1995 | h1995
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1996 | h1996
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1997 | h1997
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1998 | h1998
                                  · linarith only [h1852, h1914, h1991, h1998, hlam]
                                  · rcases h1bigk with h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c | h2000c
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1, h1975, hc12, hc23, hlam, hphi, p2000_1]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1, hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1, h1975, h1991, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2000_1, u3ehi3]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1, h1975, h1989, hc12, hc23, hlam, hphi, p2000_1]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h0, hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1975, hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1977, hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1989, hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h0, h1975, hc12, hc23, hlam, hphi, p2000_1]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      rcases p2000_3 (m.d 0 1) (by simp) with h2012 | h2012
                                      · linarith only [h1, h2012, hlam]
                                      · linarith only [h0, h2012, hlam]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      rcases p2000_3 (m.d 0 1) (by simp) with h2016 | h2016
                                      · linarith only [h1, h2016, hlam]
                                      · linarith only [h1852, h2016, hlam]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      rcases p2000_3 (m.d 0 1) (by simp) with h2019 | h2019
                                      · linarith only [h1, h2019, hlam]
                                      · linarith only [h1853, h2019, hlam]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1852, hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1852, h1914, h1997, hc12, hc24, hlam, hphi, p2000_1]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1991, hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1993, hlam, p2000_1]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1853, hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1, h1853, h1975, hc12, hc23, hlam, hphi, p2000_1]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1992, hlam, p2000_0]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [h1, h1853, h1975, h1991, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2000_1, u3ehi3]
                                    · have p2000_0 := h2000c.1
                                      have p2000_1 := h2000c.2.1
                                      have p2000_2 := h2000c.2.2.1
                                      have p2000_3 := h2000c.2.2.2
                                      linarith only [hlam, p2000_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2032 | h2032
                                  · linarith only [h1977, h1997, h2032, hc12, hc34, hlam, hphi, ht23]
                                  · rcases h1bigk with h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c | h2034c
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1, h1975, hc12, hc23, hlam, hphi, p2034_1]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1, hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1, h1975, h1991, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2034_1, u3ehi3]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1, h1975, h1992, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2034_1, u3ehi4]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h0, hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1975, hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1977, hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1989, hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h0, h1975, hc12, hc23, hlam, hphi, p2034_1]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      rcases p2034_3 (m.d 0 1) (by simp) with h2046 | h2046
                                      · linarith only [h1, h2046, hlam]
                                      · linarith only [h0, h2046, hlam]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      rcases p2034_3 (m.d 0 1) (by simp) with h2050 | h2050
                                      · linarith only [h1, h2050, hlam]
                                      · linarith only [h1852, h2050, hlam]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      rcases p2034_3 (m.d 0 1) (by simp) with h2053 | h2053
                                      · linarith only [h1, h2053, hlam]
                                      · linarith only [h1853, h2053, hlam]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1852, hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1, h1853, h1975, h1993, hc12, hc23, hlam, hphi, p2034_1]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1991, hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1993, hlam, p2034_1]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1853, hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1, h1853, h1975, hc12, hc23, hlam, hphi, p2034_1]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1992, hlam, p2034_0]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [h1, h1853, h1975, h1991, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2034_1, u3ehi3]
                                    · have p2034_0 := h2034c.1
                                      have p2034_1 := h2034c.2.1
                                      have p2034_2 := h2034c.2.2.1
                                      have p2034_3 := h2034c.2.2.2
                                      linarith only [hlam, p2034_0]
                              · linarith only [h0, h1, h1975, h1996, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h1853, h1975, h1991, h1993, h1995, hlam]
                        · linarith only [h0, h1, h1992, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h1853, h1912, h1914, h1991, hlam]
            · linarith only [h1912, h1913, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1, h1852, h1912, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2072 | h2072
      · linarith only [h0, h1, h2072, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2074 | h2074
        · linarith only [h0, h1853, h2074, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2076 | h2076
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2077 | h2077
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2078 | h2078
              · linarith only [h1852, h1853, h2078, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2080 | h2080
                · linarith only [h0, h1, h2072, h2080, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2082 | h2082
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2083 | h2083
                    · linarith only [h0, h1853, h2074, h2083, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2085 | h2085
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2086 | h2086
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2087 | h2087
                          · linarith only [h0, h1853, h2078, h2080, h2082, h2086, h2087, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h1853, h2082, h2085, h2087, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h0, h1, h2077, h2086, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h1, h2077, h2085, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2092 | h2092
                    · linarith only [h0, h2074, h2092, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2094 | h2094
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2095 | h2095
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2096 | h2096
                          · linarith only [h1852, h1853, h2078, h2095, h2096, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1852, h1853, h2094, h2096, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h1, h2077, h2095, hlam]
                      · linarith only [h1, h2077, h2094, hc34, hlam, hphi, u3ehi4]
            · linarith only [h2076, h2077, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1, h1852, h2076, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2103 | h2103
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2104 | h2104
      · linarith only [h0, h1, h2104, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2106 | h2106
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2107 | h2107
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2108 | h2108
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2109 | h2109
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2110 | h2110
                · linarith only [h0, h2104, h2106, h2110, hc01, hc25, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2112 | h2112
                  · linarith only [h0, h1852, h2112, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2114 | h2114
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2115 | h2115
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2116 | h2116
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2117 | h2117
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2118 | h2118
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2119 | h2119
                              · linarith only [h0, h1852, h2110, h2114, h2115, h2119, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h0, h1852, h2103, h2110, h2114, h2115, h2116, h2119, hc05, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h1852, h2110, h2114, h2115, h2116, h2118, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h0, h1852, h2114, h2116, h2117, hc45, hlam, hphi, ht34, u3ehi4]
                        · linarith only [h0, h1852, h2114, h2115, h2116, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1, h2107, h2114, h2115, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h1, h2106, h2110, h2114, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1852, h2106, h2109, hlam]
            · linarith only [h2107, h2108, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2129 | h2129
            · linarith only [h2107, h2129, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h1, h2106, h2129, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2132 | h2132
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2133 | h2133
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2134 | h2134
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2135 | h2135
                · linarith only [h0, h1, h2104, h2135, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2137 | h2137
                  · linarith only [h0, h1852, h2137, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2139 | h2139
                    · linarith only [h0, h2106, h2139, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2141 | h2141
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2142 | h2142
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2143 | h2143
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2144 | h2144
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2145 | h2145
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2146 | h2146
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2147 | h2147
                                  · rcases h1bigk with h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c | h2148c
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h1852, h2135, h2141, hc12, hc23, hlam, hphi, p2148_1]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h1, hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h1852, hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h1852, h2135, h2139, h2141, hc12, hc23, hlam, hphi, p2148_1]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h0, hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h2135, hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h2137, hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h2139, hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h0, h2135, hc12, hc23, hlam, hphi, p2148_1]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      rcases p2148_3 (m.d 0 1) (by simp) with h2160 | h2160
                                      · linarith only [h1, h2160, hlam]
                                      · linarith only [h0, h2160, hlam]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h1852, h2103, h2135, h2142, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2148_1, u3ehi4]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      rcases p2148_3 (m.d 0 1) (by simp) with h2165 | h2165
                                      · linarith only [h1, h2165, hlam]
                                      · linarith only [h2103, h2165, hlam]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h2103, h2142, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2148_1, u3ehi4]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      rcases p2148_3 (m.d 0 1) (by simp) with h2169 | h2169
                                      · linarith only [h1852, h2169, hlam]
                                      · linarith only [h0, h2169, hlam]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h2141, hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      rcases p2148_3 (m.d 0 1) (by simp) with h2174 | h2174
                                      · linarith only [h1852, h2174, hlam]
                                      · linarith only [h2103, h2174, hlam]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h2103, hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h1, h2103, h2135, hc12, hc23, hlam, hphi, p2148_1]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h2142, hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [h2143, hlam, p2148_0]
                                    · have p2148_0 := h2148c.1
                                      have p2148_1 := h2148c.2.1
                                      have p2148_2 := h2148c.2.2.1
                                      have p2148_3 := h2148c.2.2.2
                                      linarith only [hlam, p2148_0]
                                  · linarith only [h1852, h2103, h2135, h2141, h2143, h2147, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1852, h2103, h2135, h2137, h2141, h2143, h2146, hc12, hc23, hlam, hphi]
                              · linarith only [h1852, h2103, h2135, h2141, h2142, h2145, hlam]
                            · linarith only [h1852, h2103, h2135, h2141, h2142, h2144, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h1852, h2103, h2142, h2143, hc45, hlam, hphi, ht34, u3ehi4]
                        · linarith only [h1852, h2103, h2139, h2141, h2142, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h2103, h2132, h2139, h2141, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1852, h2103, h2134, hlam]
            · linarith only [h2132, h2133, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2191 | h2191
            · linarith only [h2132, h2191, hc34, hlam, hphi, u3ehi4]
            · linarith only [h1, h2103, h2191, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2194 | h2194
      · linarith only [h0, h1, h2194, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2196 | h2196
        · linarith only [h0, h2103, h2196, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2198 | h2198
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2199 | h2199
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2200 | h2200
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2201 | h2201
                · linarith only [h0, h1, h2194, h2201, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2203 | h2203
                  · linarith only [h0, h1852, h2203, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2205 | h2205
                    · linarith only [h0, h2103, h2196, h2205, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2207 | h2207
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2208 | h2208
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2209 | h2209
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2210 | h2210
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2211 | h2211
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2212 | h2212
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2213 | h2213
                                  · rcases h1bigk with h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c | h2214c
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h2103, h2201, h2207, h2209, hc12, hc23, hlam, hphi, p2214_1]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h1, hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h1852, hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h2103, hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h0, hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h2201, hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h2203, hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h2205, hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h0, h2201, hc12, hc23, hlam, hphi, p2214_1]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      rcases p2214_3 (m.d 0 1) (by simp) with h2226 | h2226
                                      · linarith only [h1, h2226, hlam]
                                      · linarith only [h0, h2226, hlam]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h0, h1852, h2201, hc12, hc23, hlam, hphi, p2214_1]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h0, h2103, h2201, hc12, hc23, hlam, hphi, p2214_1]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h0, h2203, hc12, hc24, hlam, hphi, p2214_1]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      rcases p2214_3 (m.d 0 1) (by simp) with h2233 | h2233
                                      · linarith only [h1852, h2233, hlam]
                                      · linarith only [h0, h2233, hlam]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h2207, hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h0, h2103, h2201, h2207, hc12, hc23, hlam, hphi, p2214_1]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h0, h2205, hc12, hc25, hlam, hphi, p2214_1]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      rcases p2214_3 (m.d 0 1) (by simp) with h2240 | h2240
                                      · linarith only [h2103, h2240, hlam]
                                      · linarith only [h0, h2240, hlam]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h2208, hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [h2209, hlam, p2214_0]
                                    · have p2214_0 := h2214c.1
                                      have p2214_1 := h2214c.2.1
                                      have p2214_2 := h2214c.2.2.1
                                      have p2214_3 := h2214c.2.2.2
                                      linarith only [hlam, p2214_0]
                                  · rcases h1bigk with h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c | h2246c
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h1, h2201, hc12, hc23, hlam, hphi, p2246_1]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h1, hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h1852, hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h2103, hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h0, hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h2201, hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h2203, hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h2205, hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h0, h2201, hc12, hc23, hlam, hphi, p2246_1]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      rcases p2246_3 (m.d 0 1) (by simp) with h2258 | h2258
                                      · linarith only [h1, h2258, hlam]
                                      · linarith only [h0, h2258, hlam]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h0, h1852, h2201, hc12, hc23, hlam, hphi, p2246_1]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h0, h2103, h2201, hc12, hc23, hlam, hphi, p2246_1]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h0, h2203, h2210, hc12, hc23, hlam, hphi, p2246_1]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      rcases p2246_3 (m.d 0 1) (by simp) with h2265 | h2265
                                      · linarith only [h1852, h2265, hlam]
                                      · linarith only [h0, h2265, hlam]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h2207, hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h0, h2103, h2203, h2210, hc12, hc23, hlam, hphi, p2246_1]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h0, h2205, h2210, h2212, hc12, hc23, hlam, hphi, p2246_1]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      rcases p2246_3 (m.d 0 1) (by simp) with h2272 | h2272
                                      · linarith only [h2103, h2272, hlam]
                                      · linarith only [h0, h2272, hlam]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h2208, hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [h2209, hlam, p2246_0]
                                    · have p2246_0 := h2246c.1
                                      have p2246_1 := h2246c.2.1
                                      have p2246_2 := h2246c.2.2.1
                                      have p2246_3 := h2246c.2.2.2
                                      linarith only [hlam, p2246_0]
                                · linarith only [h0, h1852, h2198, h2200, h2203, h2212, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h0, h1, h2201, h2211, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h2103, h2201, h2207, h2209, h2210, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1852, h2198, h2200, h2209, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h2198, h2208, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1, h2198, h2207, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2284 | h2284
                · linarith only [h0, h1852, h2284, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2286 | h2286
                  · linarith only [h0, h1852, h2200, h2286, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2288 | h2288
                    · linarith only [h0, h1852, h2196, h2200, h2288, hc02, hc45, hlam, hphi, ht23, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2290 | h2290
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2291 | h2291
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2292 | h2292
                          · linarith only [h0, h1852, h2200, h2284, h2290, h2292, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1852, h2292, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h1, h2291, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h2198, h2290, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h2198, h2199, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2298 | h2298
            · linarith only [h2198, h2298, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2300 | h2300
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2301 | h2301
                · linarith only [h0, h1, h2301, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2303 | h2303
                  · linarith only [h0, h1852, h2303, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2305 | h2305
                    · linarith only [h0, h2196, h2305, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2307 | h2307
                      · linarith only [h0, h1, h2198, h2301, h2307, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h2307, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2310 | h2310
                · linarith only [h0, h1, h2310, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2312 | h2312
                  · linarith only [h0, h1, h2198, h2300, h2312, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2314 | h2314
                    · linarith only [h0, h2196, h2314, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2316 | h2316
                      · linarith only [h0, h1, h2198, h2310, h2316, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h2316, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_13_25_L_I_L_R_H_I_x0_x0 m hb1 hb3 hb5 h0 h1
  · exact r1l7_11_13_25_L_I_L_R_H_I_x0_x1 m hb1 hb3 hb5 h0 h1

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2319 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2320 | h2320
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2321 | h2321
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2322 | h2322
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2323 | h2323
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2324 | h2324
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2325 | h2325
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2326 | h2326
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2327 | h2327
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2328 | h2328
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2329 | h2329
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2330 | h2330
                      · linarith only [h0, h2319, h2330, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h2319, h2324, h2330, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h2319, h2324, h2329, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h2319, h2324, h2328, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h2319, h2324, h2327, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2336 | h2336
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2337 | h2337
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2338 | h2338
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2339 | h2339
                      · linarith only [h0, h2319, h2339, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h2319, h2324, h2336, h2339, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h2319, h2324, h2338, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h2319, h2324, h2337, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h2319, h2324, h2336, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h2324, h2325, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2346 | h2346
            · linarith only [h2324, h2346, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2348 | h2348
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2349 | h2349
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2350 | h2350
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2351 | h2351
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2352 | h2352
                      · linarith only [h2319, h2324, h2352, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2354 | h2354
                        · linarith only [h0, h2319, h2354, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2356 | h2356
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2357 | h2357
                            · linarith only [h2319, h2346, h2349, h2357, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2359 | h2359
                              · linarith only [h0, h2320, h2346, h2349, h2354, h2356, h2359, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2361 | h2361
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2362 | h2362
                                  · rcases h1bigk with h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [hlam, p2363_0]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h0, hlam, p2363_0]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h0, h2349, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2363_1, u3ehi2]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h0, h2350, h2361, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2363_1]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h0, h2349, h2354, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2363_1, u3ehi2]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h2319, h2349, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2363_1, u3ehi2]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [hlam, p2363_0]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      rcases p2363_3 (m.d 0 1) (by simp) with h2371 | h2371
                                      · linarith only [h0, h2371, hlam]
                                      · linarith only [h2319, h2371, hlam]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      rcases p2363_3 (m.d 0 1) (by simp) with h2374 | h2374
                                      · linarith only [h0, h2374, hlam]
                                      · linarith only [h2320, h2374, hlam]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      rcases p2363_3 (m.d 0 1) (by simp) with h2377 | h2377
                                      · linarith only [h0, h2377, hlam]
                                      · linarith only [h2321, h2377, hlam]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h2319, hlam, p2363_0]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h2349, hlam, p2363_1]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [hlam, p2363_0]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h2352, hlam, p2363_1]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h2354, hlam, p2363_1]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h2320, hlam, p2363_0]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h2350, hlam, p2363_1]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h2320, h2349, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p2363_1, u3ehi2]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [hlam, p2363_0]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h0, h2320, h2349, h2354, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2363_1, u3ehi2]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h2321, hlam, p2363_0]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h2351, hlam, p2363_1]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h0, h2321, h2349, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2363_1, u3ehi2]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [h2356, hlam, p2363_0]
                                    · have p2363_0 := h2363c.1
                                      have p2363_1 := h2363c.2.1
                                      have p2363_2 := h2363c.2.2.1
                                      have p2363_3 := h2363c.2.2.2
                                      linarith only [hlam, p2363_0]
                                  · linarith only [h2319, h2324, h2349, h2362, hc45, hlam, hphi, ht34, u3ehi2]
                                · linarith only [h0, h2320, h2356, h2361, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h2324, h2348, h2349, h2352, h2356, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h0, h2319, h2349, h2351, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2319, h2349, h2350, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h2319, h2349, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2401 | h2401
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2402 | h2402
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2403 | h2403
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2404 | h2404
                      · linarith only [h0, h2319, h2404, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2406 | h2406
                        · linarith only [h0, h2320, h2404, h2406, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2408 | h2408
                          · linarith only [h0, h2320, h2324, h2348, h2408, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2410 | h2410
                            · linarith only [h2319, h2324, h2401, h2410, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2412 | h2412
                              · linarith only [h2319, h2346, h2401, h2412, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2414 | h2414
                                · linarith only [h2320, h2348, h2402, h2414, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2416 | h2416
                                  · linarith only [h2319, h2324, h2348, h2401, h2416, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h2319, h2324, h2401, h2416, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h0, h2319, h2401, h2403, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2319, h2401, h2402, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h2319, h2401, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h0, h2321, h2323, hlam]
      · linarith only [h0, h2319, h2322, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2424 | h2424
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2425 | h2425
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2426 | h2426
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2427 | h2427
            · linarith only [h2319, h2321, h2427, hlam]
            · linarith only [h2426, h2427, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2430 | h2430
            · linarith only [h2426, h2430, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2432 | h2432
              · linarith only [h2320, h2321, h2432, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2434 | h2434
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2435 | h2435
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2436 | h2436
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2437 | h2437
                      · linarith only [h2319, h2321, h2437, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2439 | h2439
                        · linarith only [h2320, h2321, h2430, h2436, h2437, h2439, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h2319, h2321, h2434, h2439, hc35, hlam, hphi, u3ehi2]
                    · linarith only [h0, h2319, h2425, h2434, h2436, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2319, h2434, h2435, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h2319, h2434, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2445 | h2445
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2446 | h2446
            · linarith only [h0, h2319, h2425, h2446, hlam]
            · linarith only [h2445, h2446, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2449 | h2449
            · linarith only [h2445, h2449, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2451 | h2451
              · linarith only [h0, h2320, h2425, h2451, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2453 | h2453
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2454 | h2454
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2455 | h2455
                    · linarith only [h0, h2319, h2425, h2453, h2455, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h2319, h2453, h2455, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2319, h2453, h2454, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h2319, h2453, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h0, h2319, h2424, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2461 | h2461
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2462 | h2462
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2463 | h2463
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2464 | h2464
          · linarith only [h2319, h2320, h2464, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2466 | h2466
            · linarith only [h2464, h2466, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2468 | h2468
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2469 | h2469
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2470 | h2470
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2471 | h2471
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2472 | h2472
                      · linarith only [h2319, h2464, h2472, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h2319, h2320, h2469, h2472, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h2319, h2320, h2469, h2470, h2471, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2319, h2470, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h2319, h2469, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h2319, h2320, h2468, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h0, h2461, h2463, hlam]
      · linarith only [h0, h2319, h2462, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2481 | h2481
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2482 | h2482
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2483 | h2483
          · linarith only [h2319, h2320, h2483, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2485 | h2485
            · linarith only [h2483, h2485, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2487 | h2487
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2488 | h2488
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2489 | h2489
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2490 | h2490
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2491 | h2491
                      · linarith only [h2319, h2320, h2483, h2489, h2491, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h2319, h2320, h2488, h2491, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h0, h2482, h2490, hlam]
                  · linarith only [h0, h2319, h2488, h2489, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h2319, h2488, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h2319, h2320, h2487, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2498 | h2498
          · linarith only [h2319, h2320, h2498, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2500 | h2500
            · linarith only [h2498, h2500, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2502 | h2502
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2503 | h2503
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2504 | h2504
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2505 | h2505
                    · linarith only [h0, h2319, h2482, h2503, h2505, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h2319, h2503, h2505, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2319, h2503, h2504, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h2319, h2503, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h2319, h2320, h2502, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h2319, h2481, hlam]

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2319 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2512 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2513 | h2513
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2514 | h2514
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2515 | h2515
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2516 | h2516
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2517 | h2517
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2518 | h2518
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2519 | h2519
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2520 | h2520
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2521 | h2521
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2522 | h2522
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2523 | h2523
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2524 | h2524
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2525 | h2525
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2526 | h2526
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2527 | h2527
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2528 | h2528
                                · rcases h1bigk with h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c | h2529c
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [hlam, p2529_0]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h0, hlam, p2529_0]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2319, hlam, p2529_0]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2319, h2521, h2524, h2526, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2529_1, u3ehi4]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2319, h2521, h2526, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2529_1, u3ehi4]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2512, h2521, h2524, h2526, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2529_1, u3ehi4]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [hlam, p2529_0]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2319, h2512, h2521, h2524, h2526, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2529_1, u3ehi4]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    rcases p2529_3 (m.d 0 1) (by simp) with h2538 | h2538
                                    · linarith only [h0, h2538, hlam]
                                    · linarith only [h2512, h2538, hlam]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    rcases p2529_3 (m.d 0 1) (by simp) with h2541 | h2541
                                    · linarith only [h0, h2541, hlam]
                                    · linarith only [h2513, h2541, hlam]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2512, h2521, h2524, h2526, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2529_1, u3ehi4]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2519, hlam, p2529_1]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [hlam, p2529_0]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    rcases p2529_3 (m.d 0 1) (by simp) with h2547 | h2547
                                    · linarith only [h2319, h2547, hlam]
                                    · linarith only [h2512, h2547, hlam]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    rcases p2529_3 (m.d 0 1) (by simp) with h2550 | h2550
                                    · linarith only [h2319, h2550, hlam]
                                    · linarith only [h2513, h2550, hlam]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2512, hlam, p2529_0]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2520, hlam, p2529_1]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2522, hlam, p2529_0]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [hlam, p2529_0]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2512, h2521, h2526, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p2529_1, u3ehi4]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2513, hlam, p2529_0]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2521, hlam, p2529_1]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2523, hlam, p2529_0]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [h2524, hlam, p2529_0]
                                  · have p2529_0 := h2529c.1
                                    have p2529_1 := h2529c.2.1
                                    have p2529_2 := h2529c.2.2.1
                                    have p2529_3 := h2529c.2.2.2
                                    linarith only [hlam, p2529_0]
                                · linarith only [h2319, h2512, h2518, h2519, h2528, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h2319, h2512, h2519, h2524, h2527, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h2319, h2513, h2519, h2523, h2526, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h2319, h2512, h2519, h2522, h2525, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h2319, h2512, h2518, h2519, h2522, h2524, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2319, h2512, h2522, h2523, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h2319, h2512, h2516, h2522, hlam]
                  · linarith only [h2319, h2512, h2515, h2517, h2518, h2519, h2521, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h2512, h2520, hlam]
              · linarith only [h0, h2512, h2514, h2517, h2518, h2519, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2573 | h2573
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2574 | h2574
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2575 | h2575
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2576 | h2576
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2577 | h2577
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2578 | h2578
                        · linarith only [h2512, h2518, h2578, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2580 | h2580
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2581 | h2581
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2582 | h2582
                              · linarith only [h2512, h2518, h2574, h2582, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2584 | h2584
                                · linarith only [h2512, h2518, h2574, h2580, h2584, hlam]
                                · rcases h1bigk with h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c | h2586c
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [hlam, p2586_0]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h0, hlam, p2586_0]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2319, hlam, p2586_0]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2319, h2574, h2580, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2586_1, u3ehi3]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2319, h2574, h2578, h2580, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2586_1, u3ehi3]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2512, h2574, h2580, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2586_1, u3ehi3]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [hlam, p2586_0]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2319, h2513, h2574, h2578, h2580, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2586_1, u3ehi3]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    rcases p2586_3 (m.d 0 1) (by simp) with h2595 | h2595
                                    · linarith only [h0, h2595, hlam]
                                    · linarith only [h2512, h2595, hlam]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    rcases p2586_3 (m.d 0 1) (by simp) with h2598 | h2598
                                    · linarith only [h0, h2598, hlam]
                                    · linarith only [h2513, h2598, hlam]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2513, h2574, h2578, h2580, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2586_1, u3ehi3]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2573, hlam, p2586_1]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [hlam, p2586_0]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    rcases p2586_3 (m.d 0 1) (by simp) with h2604 | h2604
                                    · linarith only [h2319, h2604, hlam]
                                    · linarith only [h2512, h2604, hlam]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    rcases p2586_3 (m.d 0 1) (by simp) with h2607 | h2607
                                    · linarith only [h2319, h2607, hlam]
                                    · linarith only [h2513, h2607, hlam]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2512, hlam, p2586_0]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2574, hlam, p2586_1]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2576, hlam, p2586_0]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [hlam, p2586_0]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2578, hlam, p2586_1]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2513, hlam, p2586_0]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2575, hlam, p2586_1]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2577, hlam, p2586_0]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [h2513, h2574, h2580, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p2586_1, u3ehi3]
                                  · have p2586_0 := h2586c.1
                                    have p2586_1 := h2586c.2.1
                                    have p2586_2 := h2586c.2.2.1
                                    have p2586_3 := h2586c.2.2.2
                                    linarith only [hlam, p2586_0]
                            · linarith only [h2319, h2513, h2573, h2577, h2581, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h2516, h2518, h2580, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h2319, h2512, h2576, h2577, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h2319, h2513, h2517, h2576, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h2515, h2575, hlam]
                · linarith only [h2319, h2512, h2573, h2574, hlam]
              · linarith only [h0, h2514, h2573, hlam]
          · linarith only [h2516, h2517, hc35, hlam, hphi, u3ehi3]
        · linarith only [h2319, h2512, h2516, hlam]
      · linarith only [h0, h2513, h2515, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2630 | h2630
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2631 | h2631
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2632 | h2632
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2633 | h2633
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2634 | h2634
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2635 | h2635
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2636 | h2636
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2637 | h2637
                    · linarith only [h0, h2512, h2514, h2634, h2637, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h2512, h2514, h2631, h2634, h2637, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h2512, h2514, h2632, h2633, h2634, h2636, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h2512, h2514, h2632, h2633, h2634, h2635, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2642 | h2642
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2643 | h2643
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2644 | h2644
                    · linarith only [h0, h2512, h2634, h2644, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h2319, h2512, h2632, h2633, h2644, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h2512, h2630, h2632, h2633, h2643, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h2512, h2642, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2649 | h2649
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2650 | h2650
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2651 | h2651
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2652 | h2652
                    · linarith only [h0, h2512, h2514, h2649, h2652, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h2514, h2631, h2633, h2649, h2652, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h2513, h2514, h2631, h2633, h2649, h2651, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h2513, h2514, h2631, h2633, h2649, h2650, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2657 | h2657
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2658 | h2658
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2659 | h2659
                    · linarith only [h0, h2512, h2649, h2659, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h2319, h2512, h2631, h2659, hlam]
                  · linarith only [h0, h2513, h2630, h2631, h2633, h2658, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h2512, h2657, hlam]
          · linarith only [h2631, h2632, hc35, hlam, hphi, u3ehi3]
        · linarith only [h0, h2512, h2514, h2631, hlam]
      · linarith only [h0, h2513, h2630, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2667 | h2667
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2668 | h2668
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2669 | h2669
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2670 | h2670
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2671 | h2671
            · linarith only [h2512, h2513, h2671, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2673 | h2673
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2674 | h2674
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2675 | h2675
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2676 | h2676
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2677 | h2677
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2678 | h2678
                        · linarith only [h2512, h2513, h2671, h2673, h2677, h2678, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h2512, h2513, h2676, h2678, hc45, hlam, hphi, ht34, u3ehi3]
                      · linarith only [h0, h2319, h2512, h2667, h2670, h2676, h2677, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h2319, h2670, h2676, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h2319, h2512, h2668, h2673, h2675, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h2512, h2674, hlam]
              · linarith only [h0, h2512, h2667, h2673, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h2669, h2670, hc35, hlam, hphi, u3ehi3]
        · linarith only [h2319, h2512, h2669, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2688 | h2688
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2689 | h2689
          · linarith only [h2667, h2668, h2689, hlam]
          · linarith only [h2688, h2689, hc35, hlam, hphi, u3ehi3]
        · linarith only [h2319, h2512, h2688, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2693 | h2693
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2694 | h2694
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2695 | h2695
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2696 | h2696
            · linarith only [h2512, h2513, h2696, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2698 | h2698
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2699 | h2699
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2700 | h2700
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2701 | h2701
                    · linarith only [h2512, h2513, h2667, h2693, h2698, h2701, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h2319, h2512, h2694, h2701, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h2667, h2693, h2698, h2700, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h2512, h2513, h2667, h2693, h2694, h2698, h2699, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2706 | h2706
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2707 | h2707
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2708 | h2708
                    · linarith only [h2512, h2513, h2698, h2707, h2708, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h2319, h2694, h2708, hlam]
                  · linarith only [h0, h2512, h2693, h2694, h2707, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h2512, h2706, hlam]
          · linarith only [h2694, h2695, hc35, hlam, hphi, u3ehi3]
        · linarith only [h0, h2512, h2667, h2694, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2715 | h2715
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2716 | h2716
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2717 | h2717
            · linarith only [h2512, h2513, h2717, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2719 | h2719
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2720 | h2720
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2721 | h2721
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2722 | h2722
                    · linarith only [h0, h2512, h2667, h2719, h2722, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h2512, h2667, h2715, h2719, h2722, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h2512, h2667, h2715, h2719, h2721, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h2512, h2667, h2715, h2719, h2720, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2727 | h2727
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2728 | h2728
                  · linarith only [h0, h2512, h2693, h2715, h2719, h2728, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2730 | h2730
                    · linarith only [h0, h2512, h2719, h2730, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h2319, h2715, h2730, hlam]
                · linarith only [h0, h2512, h2727, hlam]
          · linarith only [h2715, h2716, hc35, hlam, hphi, u3ehi3]
        · linarith only [h2319, h2512, h2715, hlam]

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2319 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2512 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2736 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2737 | h2737
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2738 | h2738
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2739 | h2739
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2740 | h2740
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2741 | h2741
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2742 | h2742
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2743 | h2743
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2744 | h2744
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2745 | h2745
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2746 | h2746
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2747 | h2747
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2748 | h2748
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2749 | h2749
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2750 | h2750
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2751 | h2751
                              · rcases h1bigk with h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [hlam, p2752_0]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h0, hlam, p2752_0]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2319, hlam, p2752_0]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2512, hlam, p2752_0]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2512, h2742, h2744, h2745, h2749, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2752_1, u3ehi4]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2736, h2744, h2749, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2752_1, u3ehi4]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [hlam, p2752_0]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2319, hc01, hc12, hlam, hphi, p2752_1]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2512, h2736, h2744, h2749, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2752_1, u3ehi4]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  rcases p2752_3 (m.d 0 1) (by simp) with h2762 | h2762
                                  · linarith only [h0, h2762, hlam]
                                  · linarith only [h2736, h2762, hlam]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2736, h2744, h2749, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2752_1, u3ehi4]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2742, hlam, p2752_1]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [hlam, p2752_0]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2512, h2736, h2742, h2744, h2749, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2752_1, u3ehi4]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  rcases p2752_3 (m.d 0 1) (by simp) with h2769 | h2769
                                  · linarith only [h2319, h2769, hlam]
                                  · linarith only [h2736, h2769, hlam]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2736, h2744, h2749, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2752_1, u3ehi4]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2743, hlam, p2752_1]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2745, hlam, p2752_0]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [hlam, p2752_0]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  rcases p2752_3 (m.d 0 1) (by simp) with h2776 | h2776
                                  · linarith only [h2512, h2776, hlam]
                                  · linarith only [h2736, h2776, hlam]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2736, hlam, p2752_0]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2744, hlam, p2752_1]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2746, hlam, p2752_0]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [h2747, hlam, p2752_0]
                                · have p2752_0 := h2752c.1
                                  have p2752_1 := h2752c.2.1
                                  have p2752_2 := h2752c.2.2.1
                                  have p2752_3 := h2752c.2.2.2
                                  linarith only [hlam, p2752_0]
                              · linarith only [h0, h2736, h2747, h2751, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h2512, h2736, h2742, h2745, h2747, h2748, h2750, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h2748, h2749, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2787 | h2787
                          · linarith only [h2319, h2739, h2742, h2748, h2787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h2512, h2736, h2742, h2745, h2746, h2787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h2512, h2736, h2746, h2747, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h2319, h2739, h2746, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h2319, h2736, h2737, h2739, h2740, h2745, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h2738, h2744, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2794 | h2794
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2795 | h2795
                  · linarith only [h2742, h2743, h2795, hlam]
                  · linarith only [h2319, h2736, h2740, h2795, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h2738, h2794, hlam]
            · linarith only [h0, h2737, h2742, hlam]
          · linarith only [h2512, h2736, h2741, hlam]
        · linarith only [h2739, h2740, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2802 | h2802
        · linarith only [h2739, h2802, hc34, hlam, hphi, u3ehi4]
        · linarith only [h2319, h2736, h2802, hlam]
    · linarith only [h2319, h2736, h2737, h2738, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2806 | h2806
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2807 | h2807
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2808 | h2808
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2809 | h2809
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2810 | h2810
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2811 | h2811
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2812 | h2812
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2813 | h2813
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2814 | h2814
                    · linarith only [h0, h2736, h2737, h2810, h2814, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h2319, h2807, h2814, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h2737, h2807, h2810, h2813, hlam]
                · linarith only [h0, h2736, h2737, h2808, h2810, h2812, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · linarith only [h0, h2737, h2810, h2811, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2820 | h2820
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2821 | h2821
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2822 | h2822
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2823 | h2823
                    · linarith only [h2512, h2736, h2810, h2820, h2823, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h2319, h2807, h2823, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h2512, h2736, h2807, h2808, h2810, h2820, h2822, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h2512, h2736, h2806, h2808, h2820, h2821, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2828 | h2828
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2829 | h2829
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2830 | h2830
                    · linarith only [h0, h2736, h2810, h2830, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h2319, h2807, h2830, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h2736, h2807, h2808, h2810, h2829, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h2806, h2828, hlam]
          · linarith only [h2512, h2736, h2809, hlam]
        · linarith only [h2807, h2808, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2837 | h2837
        · linarith only [h2807, h2837, hc34, hlam, hphi, u3ehi4]
        · linarith only [h0, h2736, h2737, h2837, hlam]
    · linarith only [h0, h2736, h2806, hlam]

end R2N4
