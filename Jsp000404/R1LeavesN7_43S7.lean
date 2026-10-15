import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1556 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1746 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1853 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1854 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1855 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1856 | h1856
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1857 | h1857
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1858 | h1858
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1859 | h1859
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1860 | h1860
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1861 | h1861
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1862 | h1862
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1863 | h1863
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1864 | h1864
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1865 | h1865
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1866 | h1866
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1867 | h1867
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1868 | h1868
                          · rcases h1bigk with h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c | h1869c
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h0, hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1556, hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1746, hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              rcases p1869_3 (m.d 0 1) (by simp) with h1874 | h1874
                              · rcases p1869_3 (m.d 1 2) (by simp) with h1875 | h1875
                                · rcases p1869_3 (m.d 1 3) (by simp) with h1876 | h1876
                                  · rcases p1869_3 (m.d 1 4) (by simp) with h1877 | h1877
                                    · rcases p1869_3 (m.d 1 5) (by simp) with h1878 | h1878
                                      · linarith only [h1878, hlam, p1869_0]
                                      · rcases h2bigk with h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h0, hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1865, h1868, hc02, hc45, hlam, hphi, ht0b, ht5b, p1880_1]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          rcases p1880_3 (m.d 0 2) (by simp) with h1884 | h1884
                                          · rcases p1880_3 (m.d 1 2) (by simp) with h1885 | h1885
                                            · rcases p1880_3 (m.d 2 3) (by simp) with h1886 | h1886
                                              · linarith only [h1854, h1886, hlam]
                                              · linarith only [h1865, h1886, hlam]
                                            · linarith only [h1860, h1885, hlam]
                                          · linarith only [h1884, hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          rcases p1880_3 (m.d 0 2) (by simp) with h1891 | h1891
                                          · rcases p1880_3 (m.d 1 2) (by simp) with h1892 | h1892
                                            · rcases p1880_3 (m.d 2 3) (by simp) with h1893 | h1893
                                              · linarith only [h1854, h1893, hlam]
                                              · linarith only [h1866, h1893, hlam]
                                            · linarith only [h1861, h1892, hlam]
                                          · linarith only [h1891, hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h0, h1861, h1866, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1869_1, p1880_1]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1865, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1880_1]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          rcases p1880_3 (m.d 0 2) (by simp) with h1901 | h1901
                                          · linarith only [h0, h1901, hlam]
                                          · linarith only [h1855, h1901, hlam]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h0, h1861, hlam, p1869_1, p1880_2]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1854, hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1859, hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1854, h1865, h1868, hc02, hc45, hlam, hphi, ht0b, ht5b, p1880_1]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          rcases p1880_3 (m.d 0 2) (by simp) with h1909 | h1909
                                          · rcases p1880_3 (m.d 1 2) (by simp) with h1910 | h1910
                                            · rcases p1880_3 (m.d 2 3) (by simp) with h1911 | h1911
                                              · rcases p1880_3 (m.d 2 4) (by simp) with h1912 | h1912
                                                · linarith only [h1865, h1912, hlam]
                                                · linarith only [h1867, h1912, hlam]
                                              · linarith only [h1866, h1911, hlam]
                                            · linarith only [h1861, h1910, hlam]
                                          · linarith only [h1856, h1909, hlam]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1855, hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1860, hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1865, hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          rcases p1880_3 (m.d 0 2) (by simp) with h1922 | h1922
                                          · rcases p1880_3 (m.d 1 2) (by simp) with h1923 | h1923
                                            · rcases p1880_3 (m.d 2 3) (by simp) with h1924 | h1924
                                              · rcases p1880_3 (m.d 2 4) (by simp) with h1925 | h1925
                                                · rcases p1880_3 (m.d 2 5) (by simp) with h1926 | h1926
                                                  · linarith only [h1867, h1926, hlam]
                                                  · rcases h4bigk with h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1746, hlam, p1928_1]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1866, h1868, hc04, hc45, hlam, hphi, ht0b, ht5b, p1880_1, p1928_1]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      rcases p1928_3 (m.d 0 4) (by simp) with h1932 | h1932
                                                      · rcases p1928_3 (m.d 1 4) (by simp) with h1933 | h1933
                                                        · rcases p1928_3 (m.d 2 4) (by simp) with h1934 | h1934
                                                          · linarith only [h1855, h1934, hlam]
                                                          · linarith only [h1865, h1934, hlam]
                                                        · linarith only [h1862, h1933, hlam]
                                                      · linarith only [h1857, h1932, hlam]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      rcases p1928_3 (m.d 0 4) (by simp) with h1939 | h1939
                                                      · rcases p1928_3 (m.d 1 4) (by simp) with h1940 | h1940
                                                        · rcases p1928_3 (m.d 2 4) (by simp) with h1941 | h1941
                                                          · linarith only [h1855, h1941, hlam]
                                                          · linarith only [h1867, h1941, hlam]
                                                        · linarith only [h1864, h1940, hlam]
                                                      · linarith only [h1939, hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1746, h1861, h1862, h1866, h1868, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1869_1, p1928_1]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1859, h1862, h1866, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1880_1, p1928_1]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      rcases p1928_3 (m.d 0 4) (by simp) with h1949 | h1949
                                                      · linarith only [h1746, h1949, hlam]
                                                      · linarith only [h1857, h1949, hlam]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1746, h1861, h1866, h1868, hlam, p1869_1, p1928_2]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1855, hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1860, hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h0, h1855, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1928_1]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      rcases p1928_3 (m.d 0 4) (by simp) with h1957 | h1957
                                                      · rcases p1928_3 (m.d 1 4) (by simp) with h1958 | h1958
                                                        · rcases p1928_3 (m.d 2 4) (by simp) with h1959 | h1959
                                                          · rcases p1928_3 (m.d 3 4) (by simp) with h1960 | h1960
                                                            · linarith only [h1865, h1960, hlam]
                                                            · linarith only [h1868, h1960, hlam]
                                                          · linarith only [h1959, hlam, p1928_0]
                                                        · linarith only [h1864, h1958, hlam]
                                                      · linarith only [h1858, h1957, hlam]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1857, hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1862, hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1865, hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h0, h1854, h1865, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1928_1]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1858, hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1864, hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1867, hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [h1868, hlam, p1928_0]
                                                    · have p1928_0 := h1928c.1
                                                      have p1928_1 := h1928c.2.1
                                                      have p1928_2 := h1928c.2.2.1
                                                      have p1928_3 := h1928c.2.2.2
                                                      linarith only [hlam, p1928_0]
                                                · linarith only [h1867, h1925, hlam]
                                              · linarith only [h1866, h1924, hlam]
                                            · linarith only [h1861, h1923, hlam]
                                          · linarith only [h1856, h1922, hlam]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1856, hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1861, hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1866, hlam, p1880_0]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [h1867, hlam, p1880_1]
                                        · have p1880_0 := h1880c.1
                                          have p1880_1 := h1880c.2.1
                                          have p1880_2 := h1880c.2.2.1
                                          have p1880_3 := h1880c.2.2.2
                                          linarith only [hlam, p1880_0]
                                    · linarith only [h1864, h1877, hlam]
                                  · linarith only [h1863, h1876, hlam]
                                · linarith only [h1861, h1875, hlam]
                              · linarith only [h1874, hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              rcases p1869_3 (m.d 0 1) (by simp) with h1989 | h1989
                              · linarith only [h1989, hlam, p1869_0]
                              · rcases p1869_3 (m.d 1 2) (by simp) with h1991 | h1991
                                · rcases p1869_3 (m.d 1 3) (by simp) with h1992 | h1992
                                  · linarith only [h1859, h1992, hlam]
                                  · linarith only [h1556, h1992, hlam]
                                · linarith only [h1991, hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1556, hc01, hc12, hlam, hphi, p1869_1]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1746, h1853, h1861, h1866, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1869_1]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              rcases p1869_3 (m.d 0 1) (by simp) with h1999 | h1999
                              · linarith only [h0, h1999, hlam]
                              · linarith only [h1853, h1999, hlam]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              rcases p1869_3 (m.d 0 1) (by simp) with h2002 | h2002
                              · linarith only [h2002, hlam, p1869_0]
                              · rcases p1869_3 (m.d 1 2) (by simp) with h2004 | h2004
                                · rcases p1869_3 (m.d 1 3) (by simp) with h2005 | h2005
                                  · rcases p1869_3 (m.d 1 4) (by simp) with h2006 | h2006
                                    · linarith only [h1862, h2006, hlam]
                                    · linarith only [h1746, h2006, hlam]
                                  · linarith only [h2005, hlam, p1869_0]
                                · linarith only [h0, h2004, hlam]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1859, hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1746, h1853, h1859, h1861, h1866, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1869_1]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              rcases p1869_3 (m.d 0 1) (by simp) with h2014 | h2014
                              · linarith only [h1556, h2014, hlam]
                              · linarith only [h1853, h2014, hlam]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              rcases p1869_3 (m.d 0 1) (by simp) with h2017 | h2017
                              · linarith only [h2017, hlam, p1869_0]
                              · rcases p1869_3 (m.d 1 2) (by simp) with h2019 | h2019
                                · rcases p1869_3 (m.d 1 3) (by simp) with h2020 | h2020
                                  · rcases p1869_3 (m.d 1 4) (by simp) with h2021 | h2021
                                    · rcases p1869_3 (m.d 1 5) (by simp) with h2022 | h2022
                                      · linarith only [h1864, h2022, hlam]
                                      · rcases h2bigk with h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h0, hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h0, h1865, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2024_1]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          rcases p2024_3 (m.d 0 2) (by simp) with h2028 | h2028
                                          · rcases p2024_3 (m.d 1 2) (by simp) with h2029 | h2029
                                            · rcases p2024_3 (m.d 2 3) (by simp) with h2030 | h2030
                                              · linarith only [h1854, h2030, hlam]
                                              · linarith only [h1865, h2030, hlam]
                                            · linarith only [h1860, h2029, hlam]
                                          · linarith only [h2028, hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          rcases p2024_3 (m.d 0 2) (by simp) with h2035 | h2035
                                          · rcases p2024_3 (m.d 1 2) (by simp) with h2036 | h2036
                                            · rcases p2024_3 (m.d 2 3) (by simp) with h2037 | h2037
                                              · linarith only [h1854, h2037, hlam]
                                              · linarith only [h1866, h2037, hlam]
                                            · linarith only [h1861, h2036, hlam]
                                          · linarith only [h2035, hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1854, h1865, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2024_1]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1865, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2024_1]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          rcases p2024_3 (m.d 0 2) (by simp) with h2045 | h2045
                                          · linarith only [h0, h2045, hlam]
                                          · linarith only [h1855, h2045, hlam]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1853, h1859, h1861, h1862, hlam, p1869_1, p2024_2]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1854, hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1859, hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1854, h1865, h1868, hc02, hc45, hlam, hphi, ht0b, ht5b, p2024_1]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          rcases p2024_3 (m.d 0 2) (by simp) with h2053 | h2053
                                          · rcases p2024_3 (m.d 1 2) (by simp) with h2054 | h2054
                                            · rcases p2024_3 (m.d 2 3) (by simp) with h2055 | h2055
                                              · rcases p2024_3 (m.d 2 4) (by simp) with h2056 | h2056
                                                · linarith only [h1865, h2056, hlam]
                                                · linarith only [h1867, h2056, hlam]
                                              · linarith only [h1866, h2055, hlam]
                                            · linarith only [h1861, h2054, hlam]
                                          · linarith only [h1856, h2053, hlam]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1855, hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1860, hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1865, hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          rcases p2024_3 (m.d 0 2) (by simp) with h2066 | h2066
                                          · rcases p2024_3 (m.d 1 2) (by simp) with h2067 | h2067
                                            · rcases p2024_3 (m.d 2 3) (by simp) with h2068 | h2068
                                              · rcases p2024_3 (m.d 2 4) (by simp) with h2069 | h2069
                                                · rcases p2024_3 (m.d 2 5) (by simp) with h2070 | h2070
                                                  · linarith only [h1867, h2070, hlam]
                                                  · rcases h4bigk with h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1746, hlam, p2072_1]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1866, h1868, hc04, hc45, hlam, hphi, ht0b, ht5b, p2024_1, p2072_1]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      rcases p2072_3 (m.d 0 4) (by simp) with h2076 | h2076
                                                      · rcases p2072_3 (m.d 1 4) (by simp) with h2077 | h2077
                                                        · rcases p2072_3 (m.d 2 4) (by simp) with h2078 | h2078
                                                          · linarith only [h1855, h2078, hlam]
                                                          · linarith only [h1865, h2078, hlam]
                                                        · linarith only [h1862, h2077, hlam]
                                                      · linarith only [h1857, h2076, hlam]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      rcases p2072_3 (m.d 0 4) (by simp) with h2083 | h2083
                                                      · rcases p2072_3 (m.d 1 4) (by simp) with h2084 | h2084
                                                        · rcases p2072_3 (m.d 2 4) (by simp) with h2085 | h2085
                                                          · linarith only [h1855, h2085, hlam]
                                                          · linarith only [h1867, h2085, hlam]
                                                        · linarith only [h1864, h2084, hlam]
                                                      · linarith only [h2083, hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1855, h1862, h1866, h1868, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2024_1, p2072_1]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1859, h1862, h1866, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2024_1, p2072_1]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      rcases p2072_3 (m.d 0 4) (by simp) with h2093 | h2093
                                                      · linarith only [h1746, h2093, hlam]
                                                      · linarith only [h1857, h2093, hlam]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1853, h1861, h1866, h1868, hlam, p1869_1, p2072_2]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1855, hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1860, hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h0, h1855, h1868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2072_1]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      rcases p2072_3 (m.d 0 4) (by simp) with h2101 | h2101
                                                      · rcases p2072_3 (m.d 1 4) (by simp) with h2102 | h2102
                                                        · rcases p2072_3 (m.d 2 4) (by simp) with h2103 | h2103
                                                          · rcases p2072_3 (m.d 3 4) (by simp) with h2104 | h2104
                                                            · linarith only [h1865, h2104, hlam]
                                                            · linarith only [h1868, h2104, hlam]
                                                          · linarith only [h2103, hlam, p2072_0]
                                                        · linarith only [h1864, h2102, hlam]
                                                      · linarith only [h1858, h2101, hlam]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1857, hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1862, hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1865, hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h0, h1854, h1865, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2072_1]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1858, hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1864, hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1867, hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [h1868, hlam, p2072_0]
                                                    · have p2072_0 := h2072c.1
                                                      have p2072_1 := h2072c.2.1
                                                      have p2072_2 := h2072c.2.2.1
                                                      have p2072_3 := h2072c.2.2.2
                                                      linarith only [hlam, p2072_0]
                                                · linarith only [h1867, h2069, hlam]
                                              · linarith only [h1866, h2068, hlam]
                                            · linarith only [h1861, h2067, hlam]
                                          · linarith only [h1856, h2066, hlam]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1856, hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1861, hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1866, hlam, p2024_0]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [h1867, hlam, p2024_1]
                                        · have p2024_0 := h2024c.1
                                          have p2024_1 := h2024c.2.1
                                          have p2024_2 := h2024c.2.2.1
                                          have p2024_3 := h2024c.2.2.2
                                          linarith only [hlam, p2024_0]
                                    · linarith only [h2021, hlam, p1869_0]
                                  · linarith only [h1556, h2020, hlam]
                                · linarith only [h0, h2019, hlam]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1860, hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1862, hlam, p1869_1]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              rcases p1869_3 (m.d 0 1) (by simp) with h2135 | h2135
                              · linarith only [h1746, h2135, hlam]
                              · linarith only [h1853, h2135, hlam]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1853, hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1861, hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1863, hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [h1864, hlam, p1869_0]
                            · have p1869_0 := h1869c.1
                              have p1869_1 := h1869c.2.1
                              have p1869_2 := h1869c.2.2.1
                              have p1869_3 := h1869c.2.2.2
                              linarith only [hlam, p1869_0]
                          · linarith only [h1868, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1864, h1867, hc24, hlam, hphi, ht45, u5elo1]
                      · linarith only [h1866, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2146 | h2146
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2147 | h2147
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2148 | h2148
                          · rcases h1bigk with h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c | h2149c
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h0, hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1556, hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1746, hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              rcases p2149_3 (m.d 0 1) (by simp) with h2154 | h2154
                              · rcases p2149_3 (m.d 1 2) (by simp) with h2155 | h2155
                                · rcases p2149_3 (m.d 1 3) (by simp) with h2156 | h2156
                                  · rcases p2149_3 (m.d 1 4) (by simp) with h2157 | h2157
                                    · rcases p2149_3 (m.d 1 5) (by simp) with h2158 | h2158
                                      · linarith only [h2158, hlam, p2149_0]
                                      · rcases h2bigk with h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c | h2160c
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h0, hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          rcases p2160_3 (m.d 0 2) (by simp) with h2163 | h2163
                                          · rcases p2160_3 (m.d 1 2) (by simp) with h2164 | h2164
                                            · rcases p2160_3 (m.d 2 3) (by simp) with h2165 | h2165
                                              · linarith only [h2165, hlam, p2160_0]
                                              · rcases p2160_3 (m.d 2 4) (by simp) with h2167 | h2167
                                                · linarith only [h1855, h2167, hlam]
                                                · linarith only [h1865, h2167, hlam]
                                            · linarith only [h1859, h2164, hlam]
                                          · linarith only [h2163, hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          rcases p2160_3 (m.d 0 2) (by simp) with h2172 | h2172
                                          · rcases p2160_3 (m.d 1 2) (by simp) with h2173 | h2173
                                            · rcases p2160_3 (m.d 2 3) (by simp) with h2174 | h2174
                                              · linarith only [h1854, h2174, hlam]
                                              · rcases p2160_3 (m.d 2 4) (by simp) with h2176 | h2176
                                                · linarith only [h2176, hlam, p2160_0]
                                                · rcases p2160_3 (m.d 2 5) (by simp) with h2178 | h2178
                                                  · linarith only [h1856, h2178, hlam]
                                                  · rcases h4bigk with h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c | h2180c
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1746, hlam, p2180_1]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      rcases p2180_3 (m.d 0 4) (by simp) with h2183 | h2183
                                                      · rcases p2180_3 (m.d 1 4) (by simp) with h2184 | h2184
                                                        · rcases p2180_3 (m.d 2 4) (by simp) with h2185 | h2185
                                                          · linarith only [h1855, h2185, hlam]
                                                          · rcases p2180_3 (m.d 3 4) (by simp) with h2187 | h2187
                                                            · linarith only [h1857, h2187, hlam]
                                                            · linarith only [h1865, h2187, hlam]
                                                        · linarith only [h1860, h2184, hlam]
                                                      · linarith only [h1855, h2183, hlam]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1857, h1865, h2146, h2148, hc03, hc45, hlam, hphi, ht0b, ht5b, p2180_1]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      rcases p2180_3 (m.d 0 4) (by simp) with h2193 | h2193
                                                      · rcases p2180_3 (m.d 1 4) (by simp) with h2194 | h2194
                                                        · rcases p2180_3 (m.d 2 4) (by simp) with h2195 | h2195
                                                          · linarith only [h1855, h2195, hlam]
                                                          · linarith only [h2147, h2195, hlam]
                                                        · linarith only [h1864, h2194, hlam]
                                                      · linarith only [h2193, hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1746, h1859, h1862, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p2149_1, p2180_1]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      rcases p2180_3 (m.d 0 4) (by simp) with h2202 | h2202
                                                      · linarith only [h1746, h2202, hlam]
                                                      · linarith only [h1855, h2202, hlam]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1859, h1862, h1865, h2146, h2148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2180_1]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1746, h1861, h2146, h2148, hlam, p2149_1, p2180_2]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1855, hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1860, hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1865, hlam, p2180_1]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2160_1, p2180_1]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1857, hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1862, hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1854, h1857, hlam, p2160_2, p2180_1]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      rcases p2180_3 (m.d 0 4) (by simp) with h2216 | h2216
                                                      · rcases p2180_3 (m.d 1 4) (by simp) with h2217 | h2217
                                                        · rcases p2180_3 (m.d 2 4) (by simp) with h2218 | h2218
                                                          · linarith only [h1865, h2218, hlam]
                                                          · linarith only [h2147, h2218, hlam]
                                                        · linarith only [h1864, h2217, hlam]
                                                      · linarith only [h1858, h2216, hlam]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1858, hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h1864, hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h2147, hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [h2148, hlam, p2180_0]
                                                    · have p2180_0 := h2180c.1
                                                      have p2180_1 := h2180c.2.1
                                                      have p2180_2 := h2180c.2.2.1
                                                      have p2180_3 := h2180c.2.2.2
                                                      linarith only [hlam, p2180_0]
                                            · linarith only [h1860, h2173, hlam]
                                          · linarith only [h2172, hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          rcases p2160_3 (m.d 0 2) (by simp) with h2230 | h2230
                                          · rcases p2160_3 (m.d 1 2) (by simp) with h2231 | h2231
                                            · rcases p2160_3 (m.d 2 3) (by simp) with h2232 | h2232
                                              · linarith only [h1854, h2232, hlam]
                                              · linarith only [h2146, h2232, hlam]
                                            · linarith only [h1861, h2231, hlam]
                                          · linarith only [h2230, hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h1854, h1857, h1865, h2146, h2148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2160_1]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          rcases p2160_3 (m.d 0 2) (by simp) with h2239 | h2239
                                          · linarith only [h0, h2239, hlam]
                                          · linarith only [h1854, h2239, hlam]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          rcases p2160_3 (m.d 0 2) (by simp) with h2242 | h2242
                                          · linarith only [h0, h2242, hlam]
                                          · linarith only [h1855, h2242, hlam]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h0, h1861, hlam, p2149_1, p2160_2]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h1854, hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h1859, hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h1865, hlam, p2160_1]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h1854, h1857, h1865, hc02, hc25, hlam, hphi, ht0b, ht5b, p2160_1]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h1855, hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h1860, hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h0, h1854, h1857, h1865, h2146, h2148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2160_1]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          rcases p2160_3 (m.d 0 2) (by simp) with h2255 | h2255
                                          · rcases p2160_3 (m.d 1 2) (by simp) with h2256 | h2256
                                            · rcases p2160_3 (m.d 2 3) (by simp) with h2257 | h2257
                                              · linarith only [h1865, h2257, hlam]
                                              · linarith only [h2146, h2257, hlam]
                                            · linarith only [h1861, h2256, hlam]
                                          · linarith only [h1856, h2255, hlam]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h1856, hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h1861, hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h2146, hlam, p2160_0]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [h2147, hlam, p2160_1]
                                        · have p2160_0 := h2160c.1
                                          have p2160_1 := h2160c.2.1
                                          have p2160_2 := h2160c.2.2.1
                                          have p2160_3 := h2160c.2.2.2
                                          linarith only [hlam, p2160_0]
                                    · linarith only [h1864, h2157, hlam]
                                  · linarith only [h1863, h2156, hlam]
                                · linarith only [h1861, h2155, hlam]
                              · linarith only [h2154, hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              rcases p2149_3 (m.d 0 1) (by simp) with h2271 | h2271
                              · linarith only [h2271, hlam, p2149_0]
                              · rcases p2149_3 (m.d 1 2) (by simp) with h2273 | h2273
                                · rcases p2149_3 (m.d 1 3) (by simp) with h2274 | h2274
                                  · linarith only [h1859, h2274, hlam]
                                  · linarith only [h1556, h2274, hlam]
                                · linarith only [h2273, hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1556, hc01, hc12, hlam, hphi, p2149_1]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1746, h1853, h1861, h2146, h2148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2149_1]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              rcases p2149_3 (m.d 0 1) (by simp) with h2281 | h2281
                              · linarith only [h0, h2281, hlam]
                              · linarith only [h1853, h2281, hlam]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              rcases p2149_3 (m.d 0 1) (by simp) with h2284 | h2284
                              · linarith only [h2284, hlam, p2149_0]
                              · rcases p2149_3 (m.d 1 2) (by simp) with h2286 | h2286
                                · rcases p2149_3 (m.d 1 3) (by simp) with h2287 | h2287
                                  · rcases p2149_3 (m.d 1 4) (by simp) with h2288 | h2288
                                    · linarith only [h1862, h2288, hlam]
                                    · linarith only [h1746, h2288, hlam]
                                  · linarith only [h2287, hlam, p2149_0]
                                · linarith only [h0, h2286, hlam]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1859, hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1746, h1857, h1859, h1865, h2146, h2148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2149_1]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              rcases p2149_3 (m.d 0 1) (by simp) with h2296 | h2296
                              · linarith only [h1556, h2296, hlam]
                              · linarith only [h1853, h2296, hlam]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              rcases p2149_3 (m.d 0 1) (by simp) with h2299 | h2299
                              · linarith only [h2299, hlam, p2149_0]
                              · rcases p2149_3 (m.d 1 2) (by simp) with h2301 | h2301
                                · rcases p2149_3 (m.d 1 3) (by simp) with h2302 | h2302
                                  · rcases p2149_3 (m.d 1 4) (by simp) with h2303 | h2303
                                    · rcases p2149_3 (m.d 1 5) (by simp) with h2304 | h2304
                                      · linarith only [h1864, h2304, hlam]
                                      · rcases h2bigk with h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h0, hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          rcases p2306_3 (m.d 0 2) (by simp) with h2309 | h2309
                                          · rcases p2306_3 (m.d 1 2) (by simp) with h2310 | h2310
                                            · rcases p2306_3 (m.d 2 3) (by simp) with h2311 | h2311
                                              · linarith only [h2311, hlam, p2306_0]
                                              · rcases p2306_3 (m.d 2 4) (by simp) with h2313 | h2313
                                                · linarith only [h1855, h2313, hlam]
                                                · linarith only [h1865, h2313, hlam]
                                            · linarith only [h1859, h2310, hlam]
                                          · linarith only [h2309, hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          rcases p2306_3 (m.d 0 2) (by simp) with h2318 | h2318
                                          · rcases p2306_3 (m.d 1 2) (by simp) with h2319 | h2319
                                            · rcases p2306_3 (m.d 2 3) (by simp) with h2320 | h2320
                                              · linarith only [h1854, h2320, hlam]
                                              · rcases p2306_3 (m.d 2 4) (by simp) with h2322 | h2322
                                                · linarith only [h2322, hlam, p2306_0]
                                                · rcases p2306_3 (m.d 2 5) (by simp) with h2324 | h2324
                                                  · linarith only [h1856, h2324, hlam]
                                                  · rcases h4bigk with h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1746, hlam, p2326_1]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      rcases p2326_3 (m.d 0 4) (by simp) with h2329 | h2329
                                                      · rcases p2326_3 (m.d 1 4) (by simp) with h2330 | h2330
                                                        · rcases p2326_3 (m.d 2 4) (by simp) with h2331 | h2331
                                                          · linarith only [h1855, h2331, hlam]
                                                          · rcases p2326_3 (m.d 3 4) (by simp) with h2333 | h2333
                                                            · linarith only [h1857, h2333, hlam]
                                                            · linarith only [h1865, h2333, hlam]
                                                        · linarith only [h1860, h2330, hlam]
                                                      · linarith only [h1855, h2329, hlam]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1854, h1857, h1865, h2146, h2148, hc02, hc45, hlam, hphi, ht0b, ht5b, p2326_1]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      rcases p2326_3 (m.d 0 4) (by simp) with h2339 | h2339
                                                      · rcases p2326_3 (m.d 1 4) (by simp) with h2340 | h2340
                                                        · rcases p2326_3 (m.d 2 4) (by simp) with h2341 | h2341
                                                          · linarith only [h1855, h2341, hlam]
                                                          · linarith only [h2147, h2341, hlam]
                                                        · linarith only [h1864, h2340, hlam]
                                                      · linarith only [h2339, hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1857, h1865, h2146, h2148, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2326_1]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      rcases p2326_3 (m.d 0 4) (by simp) with h2348 | h2348
                                                      · linarith only [h1746, h2348, hlam]
                                                      · linarith only [h1855, h2348, hlam]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1859, h1862, h1865, h2146, h2148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2326_1]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1853, h1861, h2146, h2148, hlam, p2149_1, p2326_2]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1855, hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1860, hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1865, hlam, p2326_1]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2306_1, p2326_1]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1857, hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1862, hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1854, h1857, hlam, p2306_2, p2326_1]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      rcases p2326_3 (m.d 0 4) (by simp) with h2362 | h2362
                                                      · rcases p2326_3 (m.d 1 4) (by simp) with h2363 | h2363
                                                        · rcases p2326_3 (m.d 2 4) (by simp) with h2364 | h2364
                                                          · linarith only [h1865, h2364, hlam]
                                                          · linarith only [h2147, h2364, hlam]
                                                        · linarith only [h1864, h2363, hlam]
                                                      · linarith only [h1858, h2362, hlam]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1858, hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h1864, hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h2147, hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [h2148, hlam, p2326_0]
                                                    · have p2326_0 := h2326c.1
                                                      have p2326_1 := h2326c.2.1
                                                      have p2326_2 := h2326c.2.2.1
                                                      have p2326_3 := h2326c.2.2.2
                                                      linarith only [hlam, p2326_0]
                                            · linarith only [h1860, h2319, hlam]
                                          · linarith only [h2318, hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          rcases p2306_3 (m.d 0 2) (by simp) with h2376 | h2376
                                          · rcases p2306_3 (m.d 1 2) (by simp) with h2377 | h2377
                                            · rcases p2306_3 (m.d 2 3) (by simp) with h2378 | h2378
                                              · linarith only [h1854, h2378, hlam]
                                              · linarith only [h2146, h2378, hlam]
                                            · linarith only [h1861, h2377, hlam]
                                          · linarith only [h2376, hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h1854, h1857, h1865, h2146, h2148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2306_1]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          rcases p2306_3 (m.d 0 2) (by simp) with h2385 | h2385
                                          · linarith only [h0, h2385, hlam]
                                          · linarith only [h1854, h2385, hlam]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          rcases p2306_3 (m.d 0 2) (by simp) with h2388 | h2388
                                          · linarith only [h0, h2388, hlam]
                                          · linarith only [h1855, h2388, hlam]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h1853, h1860, h1861, hlam, p2149_1, p2306_2]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h1854, hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h1859, hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h1865, hlam, p2306_1]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h1854, h1857, h1865, hc02, hc25, hlam, hphi, ht0b, ht5b, p2306_1]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h1855, hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h1860, hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h0, h1854, h1857, h1865, h2146, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2306_1]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          rcases p2306_3 (m.d 0 2) (by simp) with h2401 | h2401
                                          · rcases p2306_3 (m.d 1 2) (by simp) with h2402 | h2402
                                            · rcases p2306_3 (m.d 2 3) (by simp) with h2403 | h2403
                                              · linarith only [h1865, h2403, hlam]
                                              · linarith only [h2146, h2403, hlam]
                                            · linarith only [h1861, h2402, hlam]
                                          · linarith only [h1856, h2401, hlam]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h1856, hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h1861, hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h2146, hlam, p2306_0]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [h2147, hlam, p2306_1]
                                        · have p2306_0 := h2306c.1
                                          have p2306_1 := h2306c.2.1
                                          have p2306_2 := h2306c.2.2.1
                                          have p2306_3 := h2306c.2.2.2
                                          linarith only [hlam, p2306_0]
                                    · linarith only [h2303, hlam, p2149_0]
                                  · linarith only [h1556, h2302, hlam]
                                · linarith only [h0, h2301, hlam]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1860, hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1862, hlam, p2149_1]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              rcases p2149_3 (m.d 0 1) (by simp) with h2419 | h2419
                              · linarith only [h1746, h2419, hlam]
                              · linarith only [h1853, h2419, hlam]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1853, hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1861, hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1863, hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [h1864, hlam, p2149_0]
                            · have p2149_0 := h2149c.1
                              have p2149_1 := h2149c.2.1
                              have p2149_2 := h2149c.2.2.1
                              have p2149_3 := h2149c.2.2.2
                              linarith only [hlam, p2149_0]
                          · linarith only [h1865, h2148, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1864, h2147, hc24, hlam, hphi, ht45, u5elo1]
                      · linarith only [h2146, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h1746, h1864, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h1746, h1853, h1861, h1862, h1863, hc25, hlam, hphi, u5elo3]
              · linarith only [h1556, h1853, h1854, h1857, h1861, h1862, hc02, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h1861, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h1556, h1853, h1855, h1859, h1860, hc02, hc15, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h1854, h1859, hlam]
      · linarith only [h1746, h1853, h1858, hc15, hlam, hphi, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2437 | h2437
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2438 | h2438
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2439 | h2439
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2440 | h2440
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2441 | h2441
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2442 | h2442
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2443 | h2443
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2444 | h2444
                    · linarith only [h1854, h1857, h2444, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2446 | h2446
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2447 | h2447
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2448 | h2448
                          · rcases h1bigk with h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h0, hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h1556, hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h1746, hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h1556, h1857, h2438, h2440, h2441, h2446, h2448, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2449_1]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              rcases p2449_3 (m.d 0 1) (by simp) with h2455 | h2455
                              · linarith only [h2455, hlam, p2449_0]
                              · rcases p2449_3 (m.d 1 2) (by simp) with h2457 | h2457
                                · rcases p2449_3 (m.d 1 3) (by simp) with h2458 | h2458
                                  · linarith only [h2438, h2458, hlam]
                                  · linarith only [h1556, h2458, hlam]
                                · linarith only [h2457, hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h1556, h1857, h2441, hc01, hc12, hlam, hphi, p2449_1]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h1556, h1853, h1857, h2440, h2441, h2446, h2448, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2449_1]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h1556, h1853, h1857, h2438, h2441, hlam, p2449_2]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              rcases p2449_3 (m.d 0 1) (by simp) with h2466 | h2466
                              · linarith only [h2466, hlam, p2449_0]
                              · rcases p2449_3 (m.d 1 2) (by simp) with h2468 | h2468
                                · rcases p2449_3 (m.d 1 3) (by simp) with h2469 | h2469
                                  · rcases p2449_3 (m.d 1 4) (by simp) with h2470 | h2470
                                    · linarith only [h2441, h2470, hlam]
                                    · linarith only [h1746, h2470, hlam]
                                  · linarith only [h2469, hlam, p2449_0]
                                · linarith only [h0, h2468, hlam]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h2438, hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h1556, h1853, h1857, h2438, h2440, h2441, h2446, h2448, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2449_1]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h1556, h1853, h1857, h2441, hlam, p2449_2]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              rcases p2449_3 (m.d 0 1) (by simp) with h2479 | h2479
                              · linarith only [h2479, hlam, p2449_0]
                              · rcases p2449_3 (m.d 1 2) (by simp) with h2481 | h2481
                                · rcases p2449_3 (m.d 1 3) (by simp) with h2482 | h2482
                                  · rcases p2449_3 (m.d 1 4) (by simp) with h2483 | h2483
                                    · rcases p2449_3 (m.d 1 5) (by simp) with h2484 | h2484
                                      · linarith only [h2443, h2484, hlam]
                                      · rcases h2bigk with h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c | h2486c
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h0, hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          rcases p2486_3 (m.d 0 2) (by simp) with h2489 | h2489
                                          · rcases p2486_3 (m.d 1 2) (by simp) with h2490 | h2490
                                            · rcases p2486_3 (m.d 2 3) (by simp) with h2491 | h2491
                                              · linarith only [h2491, hlam, p2486_0]
                                              · rcases p2486_3 (m.d 2 4) (by simp) with h2493 | h2493
                                                · linarith only [h1855, h2493, hlam]
                                                · linarith only [h2444, h2493, hlam]
                                            · linarith only [h2438, h2490, hlam]
                                          · linarith only [h2489, hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          rcases p2486_3 (m.d 0 2) (by simp) with h2498 | h2498
                                          · rcases p2486_3 (m.d 1 2) (by simp) with h2499 | h2499
                                            · rcases p2486_3 (m.d 2 3) (by simp) with h2500 | h2500
                                              · linarith only [h1854, h2500, hlam]
                                              · rcases p2486_3 (m.d 2 4) (by simp) with h2502 | h2502
                                                · linarith only [h2502, hlam, p2486_0]
                                                · rcases p2486_3 (m.d 2 5) (by simp) with h2504 | h2504
                                                  · linarith only [h1856, h2504, hlam]
                                                  · rcases h4bigk with h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h1746, hlam, p2506_1]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h1857, h2441, h2444, h2446, h2448, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2506_1]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h1857, hlam, p2506_1]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      rcases p2506_3 (m.d 0 4) (by simp) with h2511 | h2511
                                                      · rcases p2506_3 (m.d 1 4) (by simp) with h2512 | h2512
                                                        · rcases p2506_3 (m.d 2 4) (by simp) with h2513 | h2513
                                                          · linarith only [h1855, h2513, hlam]
                                                          · linarith only [h2447, h2513, hlam]
                                                        · linarith only [h2443, h2512, hlam]
                                                      · linarith only [h2511, hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      rcases p2506_3 (m.d 0 4) (by simp) with h2518 | h2518
                                                      · linarith only [h1746, h2518, hlam]
                                                      · rcases p2506_3 (m.d 1 4) (by simp) with h2520 | h2520
                                                        · rcases p2506_3 (m.d 2 4) (by simp) with h2521 | h2521
                                                          · linarith only [h2439, h2521, hlam]
                                                          · rcases p2506_3 (m.d 3 4) (by simp) with h2523 | h2523
                                                            · linarith only [h2441, h2523, hlam]
                                                            · linarith only [h1857, h2523, hlam]
                                                        · linarith only [h1746, h2520, hlam]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      rcases p2506_3 (m.d 0 4) (by simp) with h2528 | h2528
                                                      · linarith only [h1746, h2528, hlam]
                                                      · linarith only [h1855, h2528, hlam]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h1556, h1853, h1857, h2438, h2440, h2441, h2446, h2448, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2506_1]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h1853, h2440, h2446, h2448, hlam, p2449_1, p2506_2]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h1855, hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h2439, hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h2444, hlam, p2506_1]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2486_1, p2506_1]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h1746, h1853, h2438, h2440, h2441, h2446, h2448, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2506_1]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h2441, hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h2438, h2441, h2444, h2446, h2448, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2506_1]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      rcases p2506_3 (m.d 0 4) (by simp) with h2542 | h2542
                                                      · linarith only [h1857, h2542, hlam]
                                                      · linarith only [h2437, h2542, hlam]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h2437, hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h2443, hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h2447, hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [h2448, hlam, p2506_0]
                                                    · have p2506_0 := h2506c.1
                                                      have p2506_1 := h2506c.2.1
                                                      have p2506_2 := h2506c.2.2.1
                                                      have p2506_3 := h2506c.2.2.2
                                                      linarith only [hlam, p2506_0]
                                            · linarith only [h2439, h2499, hlam]
                                          · linarith only [h2498, hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          rcases p2486_3 (m.d 0 2) (by simp) with h2552 | h2552
                                          · rcases p2486_3 (m.d 1 2) (by simp) with h2553 | h2553
                                            · rcases p2486_3 (m.d 2 3) (by simp) with h2554 | h2554
                                              · linarith only [h1854, h2554, hlam]
                                              · linarith only [h2446, h2554, hlam]
                                            · linarith only [h2440, h2553, hlam]
                                          · linarith only [h2552, hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h1854, h2446, h2448, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2486_1]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          rcases p2486_3 (m.d 0 2) (by simp) with h2561 | h2561
                                          · linarith only [h0, h2561, hlam]
                                          · linarith only [h1854, h2561, hlam]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          rcases p2486_3 (m.d 0 2) (by simp) with h2564 | h2564
                                          · linarith only [h0, h2564, hlam]
                                          · linarith only [h1855, h2564, hlam]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h1556, h1853, h1857, h2438, h2440, h2441, hlam, p2486_2]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h1854, hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h2438, hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h2444, hlam, p2486_1]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h1854, h1857, h2438, h2441, h2446, h2448, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2486_1]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h1855, hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h2439, hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h1855, h1857, h2438, h2441, h2446, h2448, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2486_1]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          rcases p2486_3 (m.d 0 2) (by simp) with h2577 | h2577
                                          · rcases p2486_3 (m.d 1 2) (by simp) with h2578 | h2578
                                            · rcases p2486_3 (m.d 2 3) (by simp) with h2579 | h2579
                                              · linarith only [h2444, h2579, hlam]
                                              · linarith only [h2446, h2579, hlam]
                                            · linarith only [h2440, h2578, hlam]
                                          · linarith only [h1856, h2577, hlam]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h1856, hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h2440, hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h2446, hlam, p2486_0]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [h2447, hlam, p2486_1]
                                        · have p2486_0 := h2486c.1
                                          have p2486_1 := h2486c.2.1
                                          have p2486_2 := h2486c.2.2.1
                                          have p2486_3 := h2486c.2.2.2
                                          linarith only [hlam, p2486_0]
                                    · linarith only [h2483, hlam, p2449_0]
                                  · linarith only [h1556, h2482, hlam]
                                · linarith only [h0, h2481, hlam]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h2439, hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h2441, hlam, p2449_1]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              rcases p2449_3 (m.d 0 1) (by simp) with h2595 | h2595
                              · linarith only [h1746, h2595, hlam]
                              · linarith only [h1853, h2595, hlam]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h1853, hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h2440, hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h2442, hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [h2443, hlam, p2449_0]
                            · have p2449_0 := h2449c.1
                              have p2449_1 := h2449c.2.1
                              have p2449_2 := h2449c.2.2.1
                              have p2449_3 := h2449c.2.2.2
                              linarith only [hlam, p2449_0]
                          · linarith only [h1855, h1857, h2448, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1556, h1853, h1857, h2438, h2441, h2443, h2444, h2447, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h2446, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h2443, hc14, hlam, hphi, ht45, u5elo4]
                · linarith only [h1556, h1857, h2441, h2442, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2608 | h2608
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2609 | h2609
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2610 | h2610
                    · linarith only [h1556, h1853, h2440, h2441, h2610, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2612 | h2612
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2613 | h2613
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2614 | h2614
                          · rcases h1bigk with h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c | h2615c
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h0, hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h1556, hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h1746, hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h1556, h2440, h2441, h2612, h2614, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2615_1]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              rcases p2615_3 (m.d 0 1) (by simp) with h2621 | h2621
                              · linarith only [h2621, hlam, p2615_0]
                              · rcases p2615_3 (m.d 1 2) (by simp) with h2623 | h2623
                                · rcases p2615_3 (m.d 1 3) (by simp) with h2624 | h2624
                                  · linarith only [h2438, h2624, hlam]
                                  · linarith only [h1556, h2624, hlam]
                                · linarith only [h2623, hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h1556, hc01, hc12, hlam, hphi, p2615_1]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h1556, h1853, h2440, h2441, h2612, h2614, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2615_1]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              rcases p2615_3 (m.d 0 1) (by simp) with h2631 | h2631
                              · linarith only [h0, h2631, hlam]
                              · linarith only [h1853, h2631, hlam]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h1853, h2440, h2441, h2612, h2614, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2615_1]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h2438, hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h2441, hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              rcases p2615_3 (m.d 0 1) (by simp) with h2638 | h2638
                              · linarith only [h1556, h2638, hlam]
                              · linarith only [h1853, h2638, hlam]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              rcases p2615_3 (m.d 0 1) (by simp) with h2641 | h2641
                              · linarith only [h2641, hlam, p2615_0]
                              · rcases p2615_3 (m.d 1 2) (by simp) with h2643 | h2643
                                · rcases p2615_3 (m.d 1 3) (by simp) with h2644 | h2644
                                  · linarith only [h2441, h2644, hlam]
                                  · linarith only [h1556, h2644, hlam]
                                · linarith only [h0, h2643, hlam]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h2439, hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h1556, h1853, h2439, h2440, h2612, h2614, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2615_1]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              rcases p2615_3 (m.d 0 1) (by simp) with h2651 | h2651
                              · linarith only [h1746, h2651, hlam]
                              · linarith only [h1853, h2651, hlam]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h1853, hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h2440, hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h2608, hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [h2609, hlam, p2615_0]
                            · have p2615_0 := h2615c.1
                              have p2615_1 := h2615c.2.1
                              have p2615_2 := h2615c.2.2.1
                              have p2615_3 := h2615c.2.2.2
                              linarith only [hlam, p2615_0]
                          · linarith only [h2614, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1556, h1853, h2441, h2609, h2610, h2613, hc23, hc34, hlam, hphi]
                      · linarith only [h2612, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h2609, hc14, hlam, hphi, ht45, u5elo4]
                · linarith only [h1556, h2608, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h2440, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h1556, h1853, h1855, h2438, h2439, hc02, hc15, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h1854, h2438, hlam]
      · linarith only [h1556, h1853, h1857, h2437, hc15, hlam, hphi, u5elo4]
  · linarith only [h1856, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

end R2N4
