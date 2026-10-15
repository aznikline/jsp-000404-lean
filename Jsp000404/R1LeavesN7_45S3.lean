import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1448 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1632 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1864 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1866 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1867 | h1867
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1868 | h1868
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1869 | h1869
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1870 | h1870
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1871 | h1871
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1872 | h1872
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1873 | h1873
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1874 | h1874
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1875 | h1875
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1876 | h1876
                    · linarith only [h1866, h1876, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1878 | h1878
                      · linarith only [h1448, h1868, h1869, h1875, h1876, h1878, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1880 | h1880
                        · linarith only [h1448, h1868, h1869, h1875, h1876, h1878, h1880, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
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
                            linarith only [h1448, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1632, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1864, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            rcases p1882_3 (m.d 0 1) (by simp) with h1888 | h1888
                            · linarith only [h1888, hlam, p1882_0]
                            · rcases p1882_3 (m.d 1 2) (by simp) with h1890 | h1890
                              · rcases p1882_3 (m.d 1 3) (by simp) with h1891 | h1891
                                · linarith only [h1869, h1891, hlam]
                                · linarith only [h1448, h1891, hlam]
                              · linarith only [h1890, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1448, hc01, hc12, hlam, hphi, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1874, h1875, h1876, h1880, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1882_1, u5ehi1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            rcases p1882_3 (m.d 0 1) (by simp) with h1899 | h1899
                            · linarith only [h1899, hlam, p1882_0]
                            · rcases p1882_3 (m.d 1 2) (by simp) with h1901 | h1901
                              · rcases p1882_3 (m.d 1 3) (by simp) with h1902 | h1902
                                · rcases p1882_3 (m.d 1 4) (by simp) with h1903 | h1903
                                  · linarith only [h1872, h1903, hlam]
                                  · linarith only [h1632, h1903, hlam]
                                · linarith only [h1902, hlam, p1882_0]
                              · linarith only [h0, h1901, hlam]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1869, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1874, h1875, h1876, h1880, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1864, h1868, h1869, h1875, h1876, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            rcases p1882_3 (m.d 0 1) (by simp) with h1912 | h1912
                            · linarith only [h1912, hlam, p1882_0]
                            · rcases p1882_3 (m.d 1 2) (by simp) with h1914 | h1914
                              · rcases p1882_3 (m.d 1 3) (by simp) with h1915 | h1915
                                · rcases p1882_3 (m.d 1 4) (by simp) with h1916 | h1916
                                  · rcases p1882_3 (m.d 1 5) (by simp) with h1917 | h1917
                                    · linarith only [h1874, h1917, hlam]
                                    · linarith only [h1864, h1917, hlam]
                                  · linarith only [h1916, hlam, p1882_0]
                                · linarith only [h1448, h1915, hlam]
                              · linarith only [h0, h1914, hlam]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1870, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1872, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1864, h1868, h1875, h1876, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            rcases p1882_3 (m.d 0 1) (by simp) with h1927 | h1927
                            · linarith only [h1927, hlam, p1882_0]
                            · rcases p1882_3 (m.d 1 2) (by simp) with h1929 | h1929
                              · rcases p1882_3 (m.d 1 3) (by simp) with h1930 | h1930
                                · rcases p1882_3 (m.d 1 4) (by simp) with h1931 | h1931
                                  · rcases p1882_3 (m.d 1 5) (by simp) with h1932 | h1932
                                    · rcases h3bigk with h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1448, hlam, p1933_1]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        rcases p1933_3 (m.d 0 3) (by simp) with h1936 | h1936
                                        · rcases p1933_3 (m.d 1 3) (by simp) with h1937 | h1937
                                          · rcases p1933_3 (m.d 2 3) (by simp) with h1938 | h1938
                                            · linarith only [h1866, h1938, hlam]
                                            · rcases p1933_3 (m.d 3 4) (by simp) with h1940 | h1940
                                              · linarith only [h1867, h1940, hlam]
                                              · rcases p1933_3 (m.d 3 5) (by simp) with h1942 | h1942
                                                · linarith only [h1868, h1942, hlam]
                                                · linarith only [h1876, h1942, hlam]
                                          · linarith only [h1869, h1937, hlam]
                                        · linarith only [h1866, h1936, hlam]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1868, h1875, h1876, hlam, p1933_2]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1866, h1875, h1876, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1933_1]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1868, h1869, h1875, h1876, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1933_1]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        rcases p1933_3 (m.d 0 3) (by simp) with h1951 | h1951
                                        · linarith only [h1448, h1951, hlam]
                                        · linarith only [h1866, h1951, hlam]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1448, h1868, h1875, h1876, hlam, p1933_2]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1875, h1876, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1933_1]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1866, hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1869, hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1868, h1876, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1933_1]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1876, hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1867, hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1872, hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1875, hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1880, hlam, p1933_1]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1868, hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1873, hlam, p1933_0]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [h1869, h1872, h1874, h1875, h1880, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1933_1]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        rcases p1933_3 (m.d 0 3) (by simp) with h1969 | h1969
                                        · rcases p1933_3 (m.d 1 3) (by simp) with h1970 | h1970
                                          · rcases p1933_3 (m.d 2 3) (by simp) with h1971 | h1971
                                            · linarith only [h1876, h1971, hlam]
                                            · linarith only [h1875, h1971, hlam]
                                          · linarith only [h1872, h1970, hlam]
                                        · linarith only [h1867, h1969, hlam]
                                      · have p1933_0 := h1933c.1
                                        have p1933_1 := h1933c.2.1
                                        have p1933_2 := h1933c.2.2.1
                                        have p1933_3 := h1933c.2.2.2
                                        linarith only [hlam, p1933_0]
                                    · linarith only [h1932, hlam, p1882_0]
                                  · linarith only [h1632, h1931, hlam]
                                · linarith only [h1448, h1930, hlam]
                              · linarith only [h0, h1929, hlam]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1871, hlam, p1882_1]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1873, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [h1874, hlam, p1882_0]
                          · have p1882_0 := h1882c.1
                            have p1882_1 := h1882c.2.1
                            have p1882_2 := h1882c.2.2.1
                            have p1882_3 := h1882c.2.2.2
                            linarith only [hlam, p1882_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1985 | h1985
                    · linarith only [h1867, h1875, h1985, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1987 | h1987
                      · linarith only [h1870, h1987, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1989 | h1989
                        · linarith only [h0, h1866, h1867, h1989, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases h1bigk with h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c | h1991c
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h0, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1448, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1632, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1864, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            rcases p1991_3 (m.d 0 1) (by simp) with h1997 | h1997
                            · linarith only [h1997, hlam, p1991_0]
                            · rcases p1991_3 (m.d 1 2) (by simp) with h1999 | h1999
                              · rcases p1991_3 (m.d 1 3) (by simp) with h2000 | h2000
                                · linarith only [h1869, h2000, hlam]
                                · linarith only [h1448, h2000, hlam]
                              · linarith only [h1999, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1448, hc01, hc12, hlam, hphi, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1632, hc01, hc12, hlam, hphi, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1991_1, u5ehi1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            rcases p1991_3 (m.d 0 1) (by simp) with h2008 | h2008
                            · linarith only [h2008, hlam, p1991_0]
                            · rcases p1991_3 (m.d 1 2) (by simp) with h2010 | h2010
                              · rcases p1991_3 (m.d 1 3) (by simp) with h2011 | h2011
                                · rcases p1991_3 (m.d 1 4) (by simp) with h2012 | h2012
                                  · linarith only [h1872, h2012, hlam]
                                  · linarith only [h1632, h2012, hlam]
                                · linarith only [h2011, hlam, p1991_0]
                              · linarith only [h0, h2010, hlam]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1869, hlam, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1874, h1875, h1989, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1864, h1868, h1869, h1985, hc12, hlam, hphi, ht01, ht0b, ht5b, p1991_1, u5ehi2]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            rcases p1991_3 (m.d 0 1) (by simp) with h2021 | h2021
                            · linarith only [h2021, hlam, p1991_0]
                            · rcases p1991_3 (m.d 1 2) (by simp) with h2023 | h2023
                              · rcases p1991_3 (m.d 1 3) (by simp) with h2024 | h2024
                                · rcases p1991_3 (m.d 1 4) (by simp) with h2025 | h2025
                                  · rcases p1991_3 (m.d 1 5) (by simp) with h2026 | h2026
                                    · linarith only [h1874, h2026, hlam]
                                    · linarith only [h1864, h2026, hlam]
                                  · linarith only [h2025, hlam, p1991_0]
                                · linarith only [h1448, h2024, hlam]
                              · linarith only [h0, h2023, hlam]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1870, hlam, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1872, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1864, h1868, h1985, hc14, hlam, hphi, ht01, ht0b, ht5b, p1991_1, u5ehi2]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            rcases p1991_3 (m.d 0 1) (by simp) with h2036 | h2036
                            · linarith only [h2036, hlam, p1991_0]
                            · rcases p1991_3 (m.d 1 2) (by simp) with h2038 | h2038
                              · rcases p1991_3 (m.d 1 3) (by simp) with h2039 | h2039
                                · rcases p1991_3 (m.d 1 4) (by simp) with h2040 | h2040
                                  · rcases p1991_3 (m.d 1 5) (by simp) with h2041 | h2041
                                    · rcases h3bigk with h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1448, hlam, p2042_1]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        rcases p2042_3 (m.d 0 3) (by simp) with h2045 | h2045
                                        · rcases p2042_3 (m.d 1 3) (by simp) with h2046 | h2046
                                          · rcases p2042_3 (m.d 2 3) (by simp) with h2047 | h2047
                                            · linarith only [h1866, h2047, hlam]
                                            · rcases p2042_3 (m.d 3 4) (by simp) with h2049 | h2049
                                              · linarith only [h1867, h2049, hlam]
                                              · linarith only [h1875, h2049, hlam]
                                          · linarith only [h1869, h2046, hlam]
                                        · linarith only [h1866, h2045, hlam]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        rcases p2042_3 (m.d 0 3) (by simp) with h2054 | h2054
                                        · rcases p2042_3 (m.d 1 3) (by simp) with h2055 | h2055
                                          · rcases p2042_3 (m.d 2 3) (by simp) with h2056 | h2056
                                            · linarith only [h1866, h2056, hlam]
                                            · rcases p2042_3 (m.d 3 4) (by simp) with h2058 | h2058
                                              · linarith only [h2058, hlam, p2042_0]
                                              · rcases p2042_3 (m.d 3 5) (by simp) with h2060 | h2060
                                                · linarith only [h1868, h2060, hlam]
                                                · linarith only [h1989, h2060, hlam]
                                          · linarith only [h1872, h2055, hlam]
                                        · linarith only [h2054, hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1985, hc03, hlam, hphi, ht0b, ht5b, p2042_1, u5ehi2]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1867, h1869, h1875, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2042_1]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1872, h1874, h1875, h1989, hlam, p2042_2]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        rcases p2042_3 (m.d 0 3) (by simp) with h2069 | h2069
                                        · linarith only [h1448, h2069, hlam]
                                        · linarith only [h1867, h2069, hlam]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1985, hc13, hlam, hphi, ht01, ht0b, ht5b, p2042_1, u5ehi2]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1866, hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1869, hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1875, hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1985, hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1867, hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1872, hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1874, h1989, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2042_1]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1989, hlam, p2042_1]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1868, hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1873, hlam, p2042_0]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        rcases p2042_3 (m.d 0 3) (by simp) with h2085 | h2085
                                        · rcases p2042_3 (m.d 1 3) (by simp) with h2086 | h2086
                                          · rcases p2042_3 (m.d 2 3) (by simp) with h2087 | h2087
                                            · linarith only [h2087, hlam, p2042_0]
                                            · rcases p2042_3 (m.d 3 4) (by simp) with h2089 | h2089
                                              · linarith only [h1989, h2089, hlam]
                                              · linarith only [h1875, h2089, hlam]
                                          · linarith only [h1869, h2086, hlam]
                                        · linarith only [h1866, h2085, hlam]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [h1868, h1875, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2042_1]
                                      · have p2042_0 := h2042c.1
                                        have p2042_1 := h2042c.2.1
                                        have p2042_2 := h2042c.2.2.1
                                        have p2042_3 := h2042c.2.2.2
                                        linarith only [hlam, p2042_0]
                                    · linarith only [h2041, hlam, p1991_0]
                                  · linarith only [h1632, h2040, hlam]
                                · linarith only [h1448, h2039, hlam]
                              · linarith only [h0, h2038, hlam]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1871, hlam, p1991_1]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1873, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [h1874, hlam, p1991_0]
                          · have p1991_0 := h1991c.1
                            have p1991_1 := h1991c.2.1
                            have p1991_2 := h1991c.2.2.1
                            have p1991_3 := h1991c.2.2.2
                            linarith only [hlam, p1991_0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2104 | h2104
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2105 | h2105
                    · linarith only [h0, h1866, h2105, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2107 | h2107
                      · linarith only [h1448, h1632, h1868, h1869, h1874, h2104, h2105, h2107, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2109 | h2109
                        · linarith only [h1448, h1864, h1867, h1869, h1874, h2109, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · rcases h1bigk with h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [hlam, p2111_0]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h0, hlam, p2111_0]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1448, hlam, p2111_0]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1632, hlam, p2111_0]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1864, hlam, p2111_0]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            rcases p2111_3 (m.d 0 1) (by simp) with h2117 | h2117
                            · linarith only [h2117, hlam, p2111_0]
                            · rcases p2111_3 (m.d 1 2) (by simp) with h2119 | h2119
                              · rcases p2111_3 (m.d 1 3) (by simp) with h2120 | h2120
                                · linarith only [h1869, h2120, hlam]
                                · linarith only [h1448, h2120, hlam]
                              · linarith only [h2119, hlam, p2111_0]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [hlam, p2111_0]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1448, h1868, h2105, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2111_1]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1632, hc01, hc12, hlam, hphi, p2111_1]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1864, h1868, h2104, h2105, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2111_1]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            rcases p2111_3 (m.d 0 1) (by simp) with h2128 | h2128
                            · linarith only [h2128, hlam, p2111_0]
                            · rcases p2111_3 (m.d 1 2) (by simp) with h2130 | h2130
                              · rcases p2111_3 (m.d 1 3) (by simp) with h2131 | h2131
                                · rcases p2111_3 (m.d 1 4) (by simp) with h2132 | h2132
                                  · linarith only [h1872, h2132, hlam]
                                  · linarith only [h1632, h2132, hlam]
                                · linarith only [h2131, hlam, p2111_0]
                              · linarith only [h0, h2130, hlam]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1869, hlam, p2111_1]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [hlam, p2111_0]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1632, hc01, hc13, hlam, hphi, p2111_1]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1864, h1868, h1869, h2104, h2105, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2111_1]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2111_1]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1870, hlam, p2111_1]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1872, hlam, p2111_0]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [hlam, p2111_0]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1874, hlam, p2111_1]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            rcases p2111_3 (m.d 0 1) (by simp) with h2146 | h2146
                            · linarith only [h2146, hlam, p2111_0]
                            · rcases p2111_3 (m.d 1 2) (by simp) with h2148 | h2148
                              · rcases p2111_3 (m.d 1 3) (by simp) with h2149 | h2149
                                · rcases p2111_3 (m.d 1 4) (by simp) with h2150 | h2150
                                  · linarith only [h1874, h2150, hlam]
                                  · linarith only [h1632, h2150, hlam]
                                · linarith only [h1448, h2149, hlam]
                              · linarith only [h0, h2148, hlam]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1871, hlam, p2111_1]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1873, hlam, p2111_0]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [h1632, hc01, hc15, hlam, hphi, p2111_1]
                          · have p2111_0 := h2111c.1
                            have p2111_1 := h2111c.2.1
                            have p2111_2 := h2111c.2.2.1
                            have p2111_3 := h2111c.2.2.2
                            linarith only [hlam, p2111_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2159 | h2159
                    · linarith only [h2104, h2159, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2161 | h2161
                      · linarith only [h1632, h1874, h2161, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2163 | h2163
                        · linarith only [h1632, h1867, h1874, h2163, hlam]
                        · rcases h1bigk with h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [hlam, p2165_0]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h0, hlam, p2165_0]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1448, hlam, p2165_0]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1632, hlam, p2165_0]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1864, hlam, p2165_0]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            rcases p2165_3 (m.d 0 1) (by simp) with h2171 | h2171
                            · linarith only [h2171, hlam, p2165_0]
                            · rcases p2165_3 (m.d 1 2) (by simp) with h2173 | h2173
                              · rcases p2165_3 (m.d 1 3) (by simp) with h2174 | h2174
                                · linarith only [h1869, h2174, hlam]
                                · linarith only [h1448, h2174, hlam]
                              · linarith only [h2173, hlam, p2165_0]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [hlam, p2165_0]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1448, hc01, hc12, hlam, hphi, p2165_1]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1632, hc01, hc12, hlam, hphi, p2165_1]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2165_1, u5ehi1]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            rcases p2165_3 (m.d 0 1) (by simp) with h2182 | h2182
                            · linarith only [h2182, hlam, p2165_0]
                            · rcases p2165_3 (m.d 1 2) (by simp) with h2184 | h2184
                              · rcases p2165_3 (m.d 1 3) (by simp) with h2185 | h2185
                                · rcases p2165_3 (m.d 1 4) (by simp) with h2186 | h2186
                                  · linarith only [h1872, h2186, hlam]
                                  · linarith only [h1632, h2186, hlam]
                                · linarith only [h2185, hlam, p2165_0]
                              · linarith only [h0, h2184, hlam]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1869, hlam, p2165_1]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [hlam, p2165_0]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1632, hc01, hc13, hlam, hphi, p2165_1]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1864, h1868, h1869, h2159, hc12, hlam, hphi, ht01, ht0b, ht5b, p2165_1, u5ehi2]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2165_1]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1870, hlam, p2165_1]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1872, hlam, p2165_0]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [hlam, p2165_0]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1874, hlam, p2165_1]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            rcases p2165_3 (m.d 0 1) (by simp) with h2200 | h2200
                            · linarith only [h2200, hlam, p2165_0]
                            · rcases p2165_3 (m.d 1 2) (by simp) with h2202 | h2202
                              · rcases p2165_3 (m.d 1 3) (by simp) with h2203 | h2203
                                · rcases p2165_3 (m.d 1 4) (by simp) with h2204 | h2204
                                  · linarith only [h1874, h2204, hlam]
                                  · linarith only [h1632, h2204, hlam]
                                · linarith only [h1448, h2203, hlam]
                              · linarith only [h0, h2202, hlam]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1871, hlam, p2165_1]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1873, hlam, p2165_0]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [h1632, hc01, hc15, hlam, hphi, p2165_1]
                          · have p2165_0 := h2165c.1
                            have p2165_1 := h2165c.2.1
                            have p2165_2 := h2165c.2.2.1
                            have p2165_3 := h2165c.2.2.2
                            linarith only [hlam, p2165_0]
              · linarith only [h1448, h1868, h1873, hlam]
            · linarith only [h1448, h1867, h1868, h1872, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
          · linarith only [h0, h1866, h1868, h1871, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
        · linarith only [h0, h1866, h1868, h1870, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
      · linarith only [h0, h1866, h1868, h1869, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2218 | h2218
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2219 | h2219
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2220 | h2220
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2221 | h2221
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2222 | h2222
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2223 | h2223
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2224 | h2224
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2225 | h2225
                    · linarith only [h1866, h1868, h2225, hc02, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2227 | h2227
                      · linarith only [h1866, h1868, h2222, h2224, h2227, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2229 | h2229
                        · linarith only [h1866, h1868, h2218, h2222, h2224, h2227, h2229, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · rcases h1bigk with h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h0, hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h1448, hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h1632, hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h1864, hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            rcases p2231_3 (m.d 0 1) (by simp) with h2237 | h2237
                            · linarith only [h2237, hlam, p2231_0]
                            · rcases p2231_3 (m.d 1 2) (by simp) with h2239 | h2239
                              · rcases p2231_3 (m.d 1 3) (by simp) with h2240 | h2240
                                · linarith only [h2218, h2240, hlam]
                                · linarith only [h1448, h2240, hlam]
                              · linarith only [h2239, hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h1868, h2221, h2223, h2229, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2231_1]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h1866, h1868, h2223, h2224, h2229, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2231_1]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2231_1, u5ehi1]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            rcases p2231_3 (m.d 0 1) (by simp) with h2248 | h2248
                            · linarith only [h2248, hlam, p2231_0]
                            · rcases p2231_3 (m.d 1 2) (by simp) with h2250 | h2250
                              · rcases p2231_3 (m.d 1 3) (by simp) with h2251 | h2251
                                · rcases p2231_3 (m.d 1 4) (by simp) with h2252 | h2252
                                  · linarith only [h2221, h2252, hlam]
                                  · linarith only [h1632, h2252, hlam]
                                · linarith only [h2251, hlam, p2231_0]
                              · linarith only [h0, h2250, hlam]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h2218, hlam, p2231_1]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h1866, h1868, h2223, h2224, h2229, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2231_1]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h1866, h1868, h2218, h2223, h2224, h2229, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2231_1]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            rcases p2231_3 (m.d 0 1) (by simp) with h2261 | h2261
                            · linarith only [h2261, hlam, p2231_0]
                            · rcases p2231_3 (m.d 1 2) (by simp) with h2263 | h2263
                              · rcases p2231_3 (m.d 1 3) (by simp) with h2264 | h2264
                                · rcases p2231_3 (m.d 1 4) (by simp) with h2265 | h2265
                                  · rcases p2231_3 (m.d 1 5) (by simp) with h2266 | h2266
                                    · linarith only [h2223, h2266, hlam]
                                    · linarith only [h1864, h2266, hlam]
                                  · linarith only [h2265, hlam, p2231_0]
                                · linarith only [h1448, h2264, hlam]
                              · linarith only [h0, h2263, hlam]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h2219, hlam, p2231_1]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h2221, hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h1866, h1868, h2223, h2224, h2229, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2231_1]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            rcases p2231_3 (m.d 0 1) (by simp) with h2276 | h2276
                            · linarith only [h2276, hlam, p2231_0]
                            · rcases p2231_3 (m.d 1 2) (by simp) with h2278 | h2278
                              · rcases p2231_3 (m.d 1 3) (by simp) with h2279 | h2279
                                · rcases p2231_3 (m.d 1 4) (by simp) with h2280 | h2280
                                  · rcases p2231_3 (m.d 1 5) (by simp) with h2281 | h2281
                                    · rcases h3bigk with h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h1448, hlam, p2282_1]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h1868, h2224, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2282_1]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h1868, h2229, hc34, hc45, hlam, hphi, p2282_1]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h1868, hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        rcases p2282_3 (m.d 0 3) (by simp) with h2288 | h2288
                                        · linarith only [h1448, h2288, hlam]
                                        · rcases p2282_3 (m.d 1 3) (by simp) with h2290 | h2290
                                          · rcases p2282_3 (m.d 2 3) (by simp) with h2291 | h2291
                                            · linarith only [h2218, h2291, hlam]
                                            · rcases p2282_3 (m.d 3 4) (by simp) with h2293 | h2293
                                              · linarith only [h2221, h2293, hlam]
                                              · rcases p2282_3 (m.d 3 5) (by simp) with h2295 | h2295
                                                · linarith only [h2222, h2295, hlam]
                                                · linarith only [h1868, h2295, hlam]
                                          · linarith only [h1448, h2290, hlam]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        rcases p2282_3 (m.d 0 3) (by simp) with h2300 | h2300
                                        · linarith only [h1448, h2300, hlam]
                                        · linarith only [h1866, h2300, hlam]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h1866, h1868, h2221, h2223, h2224, h2229, hlam, p2282_2]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h1866, h1868, h2218, h2224, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2282_1]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h1866, hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h2218, hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h1866, h1868, h2218, h2222, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2282_1]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h2225, hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h1867, hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h2221, hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h2224, hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h2229, hlam, p2282_1]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h1448, h2218, h2222, hc01, hc12, hlam, hphi, p2282_1]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h2222, hlam, p2282_0]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [h2218, h2222, h2224, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2282_1]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        rcases p2282_3 (m.d 0 3) (by simp) with h2318 | h2318
                                        · linarith only [h1868, h2318, hlam]
                                        · linarith only [h1867, h2318, hlam]
                                      · have p2282_0 := h2282c.1
                                        have p2282_1 := h2282c.2.1
                                        have p2282_2 := h2282c.2.2.1
                                        have p2282_3 := h2282c.2.2.2
                                        linarith only [hlam, p2282_0]
                                    · linarith only [h2281, hlam, p2231_0]
                                  · linarith only [h1632, h2280, hlam]
                                · linarith only [h1448, h2279, hlam]
                              · linarith only [h0, h2278, hlam]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h2220, hlam, p2231_1]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h2222, hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [h2223, hlam, p2231_0]
                          · have p2231_0 := h2231c.1
                            have p2231_1 := h2231c.2.1
                            have p2231_2 := h2231c.2.2.1
                            have p2231_3 := h2231c.2.2.2
                            linarith only [hlam, p2231_0]
                  · linarith only [h1867, h1868, h2224, hc23, hc35, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2331 | h2331
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2332 | h2332
                    · linarith only [h1866, h1868, h2332, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2334 | h2334
                      · linarith only [h1632, h2223, h2334, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2336 | h2336
                        · linarith only [h1866, h1868, h2218, h2222, h2223, h2331, h2336, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                        · rcases h1bigk with h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c | h2338c
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [hlam, p2338_0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h0, hlam, p2338_0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h1448, hlam, p2338_0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h1632, hlam, p2338_0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h1864, hlam, p2338_0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            rcases p2338_3 (m.d 0 1) (by simp) with h2344 | h2344
                            · linarith only [h2344, hlam, p2338_0]
                            · rcases p2338_3 (m.d 1 2) (by simp) with h2346 | h2346
                              · rcases p2338_3 (m.d 1 3) (by simp) with h2347 | h2347
                                · linarith only [h2218, h2347, hlam]
                                · linarith only [h1448, h2347, hlam]
                              · linarith only [h2346, hlam, p2338_0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [hlam, p2338_0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h1868, h2222, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2338_1]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h1632, hc01, hc12, hlam, hphi, p2338_1]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h1864, hc12, hlam, hphi, ht01, ht0b, ht5b, p2338_1, u5ehi0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            rcases p2338_3 (m.d 0 1) (by simp) with h2355 | h2355
                            · linarith only [h2355, hlam, p2338_0]
                            · rcases p2338_3 (m.d 1 2) (by simp) with h2357 | h2357
                              · rcases p2338_3 (m.d 1 3) (by simp) with h2358 | h2358
                                · rcases p2338_3 (m.d 1 4) (by simp) with h2359 | h2359
                                  · linarith only [h2221, h2359, hlam]
                                  · linarith only [h1632, h2359, hlam]
                                · linarith only [h2358, hlam, p2338_0]
                              · linarith only [h0, h2357, hlam]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h2218, hlam, p2338_1]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [hlam, p2338_0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h1632, hc01, hc13, hlam, hphi, p2338_1]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h1866, h1868, h2218, h2222, h2331, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2338_1]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h2223, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2338_1]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h2219, hlam, p2338_1]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h2221, hlam, p2338_0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [hlam, p2338_0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h2223, hlam, p2338_1]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            rcases p2338_3 (m.d 0 1) (by simp) with h2373 | h2373
                            · linarith only [h2373, hlam, p2338_0]
                            · rcases p2338_3 (m.d 1 2) (by simp) with h2375 | h2375
                              · rcases p2338_3 (m.d 1 3) (by simp) with h2376 | h2376
                                · rcases p2338_3 (m.d 1 4) (by simp) with h2377 | h2377
                                  · linarith only [h2223, h2377, hlam]
                                  · linarith only [h1632, h2377, hlam]
                                · linarith only [h1448, h2376, hlam]
                              · linarith only [h0, h2375, hlam]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h2220, hlam, p2338_1]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h2222, hlam, p2338_0]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [h1632, hc01, hc15, hlam, hphi, p2338_1]
                          · have p2338_0 := h2338c.1
                            have p2338_1 := h2338c.2.1
                            have p2338_2 := h2338c.2.2.1
                            have p2338_3 := h2338c.2.2.2
                            linarith only [hlam, p2338_0]
                  · linarith only [h1867, h1868, h2331, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2387 | h2387
                · linarith only [h2221, h2222, h2387, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2389 | h2389
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2390 | h2390
                    · linarith only [h1448, h1866, h2222, h2390, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2392 | h2392
                      · linarith only [h1632, h2387, h2392, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2394 | h2394
                        · linarith only [h1448, h1866, h2222, h2387, h2389, h2394, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases h1bigk with h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [hlam, p2396_0]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h0, hlam, p2396_0]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h1448, hlam, p2396_0]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h1632, hlam, p2396_0]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h1864, hlam, p2396_0]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            rcases p2396_3 (m.d 0 1) (by simp) with h2402 | h2402
                            · linarith only [h2402, hlam, p2396_0]
                            · rcases p2396_3 (m.d 1 2) (by simp) with h2404 | h2404
                              · rcases p2396_3 (m.d 1 3) (by simp) with h2405 | h2405
                                · linarith only [h2218, h2405, hlam]
                                · linarith only [h1448, h2405, hlam]
                              · linarith only [h2404, hlam, p2396_0]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [hlam, p2396_0]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h1448, hc01, hc12, hlam, hphi, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h1632, hc01, hc12, hlam, hphi, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2396_1, u5ehi1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h2222, hc01, hc35, hlam, hphi, ht12, ht23, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h2218, hlam, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [hlam, p2396_0]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h1632, h2222, h2394, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h2222, hlam, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h2221, h2222, h2394, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h2219, hlam, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h2221, hlam, p2396_0]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [hlam, p2396_0]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h2387, hlam, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            rcases p2396_3 (m.d 0 1) (by simp) with h2423 | h2423
                            · linarith only [h2423, hlam, p2396_0]
                            · rcases p2396_3 (m.d 1 2) (by simp) with h2425 | h2425
                              · rcases p2396_3 (m.d 1 3) (by simp) with h2426 | h2426
                                · linarith only [h2222, h2426, hlam]
                                · linarith only [h1448, h2426, hlam]
                              · linarith only [h0, h2425, hlam]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h2220, hlam, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h1448, hc01, hc15, hlam, hphi, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [h1632, hc01, hc15, hlam, hphi, p2396_1]
                          · have p2396_0 := h2396c.1
                            have p2396_1 := h2396c.2.1
                            have p2396_2 := h2396c.2.2.1
                            have p2396_3 := h2396c.2.2.2
                            linarith only [hlam, p2396_0]
                  · linarith only [h1867, h1868, h2389, hc23, hc35, hlam, hphi]
            · linarith only [h1448, h1867, h2221, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2436 | h2436
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2437 | h2437
              · linarith only [h1867, h1868, h2218, h2220, h2437, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2439 | h2439
                · linarith only [h2219, h2220, h2439, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2441 | h2441
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2442 | h2442
                    · linarith only [h1448, h2437, h2442, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2444 | h2444
                      · linarith only [h0, h1866, h2220, h2439, h2441, h2442, h2444, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h0, h1866, h2220, h2441, h2444, hc34, hc45, hlam, hphi]
                  · linarith only [h1867, h1868, h2441, hc23, hc35, hlam, hphi]
            · linarith only [h1448, h1867, h2436, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2449 | h2449
          · linarith only [h2219, h2449, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2451 | h2451
            · linarith only [h2218, h2219, h2451, hlam]
            · linarith only [h1867, h1868, h2451, hc13, hc35, hlam, hphi]
      · linarith only [h0, h1866, h2218, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2455 | h2455
    · linarith only [h1867, h2455, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2457 | h2457
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2458 | h2458
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2459 | h2459
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2460 | h2460
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2461 | h2461
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2462 | h2462
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2463 | h2463
                  · linarith only [h0, h1448, h1866, h1867, h2463, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2465 | h2465
                    · linarith only [h1866, h1867, h2455, h2465, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2467 | h2467
                      · linarith only [h2457, h2460, h2463, h2467, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2469 | h2469
                        · linarith only [h2457, h2460, h2467, h2469, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · linarith only [h1448, h1867, h2462, h2469, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2472 | h2472
                  · linarith only [h1866, h1867, h2472, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2474 | h2474
                    · linarith only [h1866, h1867, h2455, h2474, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2476 | h2476
                      · linarith only [h1448, h1867, h2460, h2462, h2476, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2478 | h2478
                        · linarith only [h2460, h2462, h2478, hlam]
                        · rcases h1bigk with h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c | h2480c
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [hlam, p2480_0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h0, hlam, p2480_0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h1448, hlam, p2480_0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h1632, hlam, p2480_0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h1864, hlam, p2480_0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            rcases p2480_3 (m.d 0 1) (by simp) with h2486 | h2486
                            · linarith only [h2486, hlam, p2480_0]
                            · rcases p2480_3 (m.d 1 2) (by simp) with h2488 | h2488
                              · rcases p2480_3 (m.d 1 3) (by simp) with h2489 | h2489
                                · linarith only [h2457, h2489, hlam]
                                · linarith only [h1448, h2489, hlam]
                              · linarith only [h2488, hlam, p2480_0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [hlam, p2480_0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h1448, hc01, hc12, hlam, hphi, p2480_1]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h1448, h1867, h2460, hc01, hc12, hlam, hphi, p2480_1]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h2455, h2461, hc12, hlam, hphi, ht01, ht0b, ht5b, p2480_1, u5ehi0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            rcases p2480_3 (m.d 0 1) (by simp) with h2497 | h2497
                            · linarith only [h2497, hlam, p2480_0]
                            · rcases p2480_3 (m.d 1 2) (by simp) with h2499 | h2499
                              · rcases p2480_3 (m.d 1 3) (by simp) with h2500 | h2500
                                · rcases p2480_3 (m.d 1 4) (by simp) with h2501 | h2501
                                  · linarith only [h2460, h2501, hlam]
                                  · linarith only [h1632, h2501, hlam]
                                · linarith only [h2500, hlam, p2480_0]
                              · linarith only [h0, h2499, hlam]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h2457, hlam, p2480_1]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [hlam, p2480_0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h1448, h1867, h2460, hc01, hc13, hlam, hphi, p2480_1]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h2455, h2457, h2461, hc12, hlam, hphi, ht01, ht0b, ht5b, p2480_1, u5ehi0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h2462, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2480_1]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h2458, hlam, p2480_1]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h2460, hlam, p2480_0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [hlam, p2480_0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h2462, hlam, p2480_1]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            rcases p2480_3 (m.d 0 1) (by simp) with h2515 | h2515
                            · linarith only [h2515, hlam, p2480_0]
                            · rcases p2480_3 (m.d 1 2) (by simp) with h2517 | h2517
                              · rcases p2480_3 (m.d 1 3) (by simp) with h2518 | h2518
                                · rcases p2480_3 (m.d 1 4) (by simp) with h2519 | h2519
                                  · linarith only [h2462, h2519, hlam]
                                  · linarith only [h1632, h2519, hlam]
                                · linarith only [h1448, h2518, hlam]
                              · linarith only [h0, h2517, hlam]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h2459, hlam, p2480_1]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h2461, hlam, p2480_0]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [h1632, hc01, hc15, hlam, hphi, p2480_1]
                          · have p2480_0 := h2480c.1
                            have p2480_1 := h2480c.2.1
                            have p2480_2 := h2480c.2.2.1
                            have p2480_3 := h2480c.2.2.2
                            linarith only [hlam, p2480_0]
              · linarith only [h1448, h1867, h2460, h2461, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2529 | h2529
              · linarith only [h2460, h2529, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2531 | h2531
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2532 | h2532
                  · linarith only [h1448, h2460, h2532, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2534 | h2534
                    · linarith only [h0, h1866, h2534, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2536 | h2536
                      · linarith only [h2458, h2536, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2538 | h2538
                        · rcases h1bigk with h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [hlam, p2539_0]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h0, hlam, p2539_0]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h1448, hlam, p2539_0]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h1632, hlam, p2539_0]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h1864, hlam, p2539_0]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            rcases p2539_3 (m.d 0 1) (by simp) with h2545 | h2545
                            · linarith only [h2545, hlam, p2539_0]
                            · rcases p2539_3 (m.d 1 2) (by simp) with h2547 | h2547
                              · rcases p2539_3 (m.d 1 3) (by simp) with h2548 | h2548
                                · linarith only [h2457, h2548, hlam]
                                · linarith only [h1448, h2548, hlam]
                              · linarith only [h2547, hlam, p2539_0]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [hlam, p2539_0]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h1448, hc01, hc12, hlam, hphi, p2539_1]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h2531, h2536, hc12, hlam, hphi, ht01, ht0b, ht5b, p2539_1, u5ehi2]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2539_1, u5ehi1]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h2460, hc01, hc34, hlam, hphi, ht12, ht23, p2539_1]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h2457, hlam, p2539_1]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [hlam, p2539_0]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h2460, hlam, p2539_1]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h2529, hlam, p2539_1]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            rcases p2539_3 (m.d 0 1) (by simp) with h2561 | h2561
                            · linarith only [h2561, hlam, p2539_0]
                            · rcases p2539_3 (m.d 1 2) (by simp) with h2563 | h2563
                              · rcases p2539_3 (m.d 1 3) (by simp) with h2564 | h2564
                                · linarith only [h2460, h2564, hlam]
                                · linarith only [h1448, h2564, hlam]
                              · linarith only [h0, h2563, hlam]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h2458, hlam, p2539_1]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h1448, hc01, hc14, hlam, hphi, p2539_1]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [hlam, p2539_0]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h2460, h2531, h2536, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2539_1, u5ehi2]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            rcases p2539_3 (m.d 0 1) (by simp) with h2572 | h2572
                            · linarith only [h2572, hlam, p2539_0]
                            · rcases p2539_3 (m.d 1 2) (by simp) with h2574 | h2574
                              · rcases p2539_3 (m.d 1 3) (by simp) with h2575 | h2575
                                · linarith only [h2529, h2575, hlam]
                                · linarith only [h1448, h2575, hlam]
                              · linarith only [h0, h2574, hlam]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h2459, hlam, p2539_1]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h1448, hc01, hc15, hlam, hphi, p2539_1]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [h2531, hlam, p2539_0]
                          · have p2539_0 := h2539c.1
                            have p2539_1 := h2539c.2.1
                            have p2539_2 := h2539c.2.2.1
                            have p2539_3 := h2539c.2.2.2
                            linarith only [hlam, p2539_0]
                        · linarith only [h1448, h2460, h2538, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2584 | h2584
                  · linarith only [h1448, h1866, h2460, h2584, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2586 | h2586
                    · linarith only [h1448, h1866, h2460, h2586, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2588 | h2588
                      · linarith only [h2458, h2588, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2590 | h2590
                        · linarith only [h1448, h2460, h2531, h2590, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1448, h2460, h2590, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2593 | h2593
            · linarith only [h1448, h1867, h2457, h2459, h2593, hc01, hc25, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2595 | h2595
              · linarith only [h2593, h2595, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2597 | h2597
                · linarith only [h2458, h2459, h2597, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2599 | h2599
                  · linarith only [h1866, h1867, h2599, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2601 | h2601
                    · linarith only [h1448, h2595, h2599, h2601, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2603 | h2603
                      · linarith only [h2458, h2459, h2601, h2603, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2605 | h2605
                        · linarith only [h0, h1866, h2459, h2603, h2605, hc23, hc34, hlam, hphi]
                        · linarith only [h1448, h2593, h2605, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2608 | h2608
          · linarith only [h2458, h2608, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2610 | h2610
            · linarith only [h1448, h1867, h2457, h2458, h2610, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2612 | h2612
              · linarith only [h2457, h2458, h2612, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2614 | h2614
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2615 | h2615
                  · linarith only [h1448, h2610, h2615, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2617 | h2617
                    · linarith only [h1448, h2612, h2617, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2619 | h2619
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2620 | h2620
                        · rcases h1bigk with h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [hlam, p2621_0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h0, hlam, p2621_0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h1448, hlam, p2621_0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h1632, hlam, p2621_0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h1864, hlam, p2621_0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h2608, h2615, h2619, hc01, hc34, hlam, hphi, ht12, ht23, p2621_1]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [hlam, p2621_0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h2608, h2615, h2619, hc13, hc34, hlam, hphi, p2621_1]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h2458, hlam, p2621_0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h2608, hlam, p2621_0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h2457, h2608, h2615, h2619, hc01, hc34, hlam, hphi, ht12, ht23, p2621_1]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h2457, hlam, p2621_1]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [hlam, p2621_0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h2610, hlam, p2621_1]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h2612, hlam, p2621_1]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            rcases p2621_3 (m.d 0 1) (by simp) with h2637 | h2637
                            · linarith only [h2637, hlam, p2621_0]
                            · rcases p2621_3 (m.d 1 2) (by simp) with h2639 | h2639
                              · linarith only [h2458, h2639, hlam]
                              · linarith only [h0, h2639, hlam]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p2621_1]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h1448, hc01, hc14, hlam, hphi, p2621_1]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [hlam, p2621_0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h1864, h2458, h2615, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2621_1, u5ehi0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            rcases p2621_3 (m.d 0 1) (by simp) with h2646 | h2646
                            · linarith only [h2646, hlam, p2621_0]
                            · rcases p2621_3 (m.d 1 2) (by simp) with h2648 | h2648
                              · linarith only [h2608, h2648, hlam]
                              · linarith only [h0, h2648, hlam]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h1448, h2457, hc01, hc15, hlam, hphi, p2621_1]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h1448, h2612, h2620, hc01, hc34, hlam, hphi, ht12, ht23, p2621_1]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [h2614, hlam, p2621_0]
                          · have p2621_0 := h2621c.1
                            have p2621_1 := h2621c.2.1
                            have p2621_2 := h2621c.2.2.1
                            have p2621_3 := h2621c.2.2.2
                            linarith only [hlam, p2621_0]
                        · linarith only [h1448, h2457, h2458, h2615, h2620, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h2458, h2614, h2619, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2657 | h2657
                  · linarith only [h0, h1866, h1867, h2458, h2657, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2659 | h2659
                    · linarith only [h0, h1866, h2458, h2614, h2659, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2661 | h2661
                      · linarith only [h0, h1866, h2458, h2614, h2657, h2661, hc23, hc34, hlam, hphi]
                      · linarith only [h1448, h2457, h2458, h2661, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
      · linarith only [h0, h1866, h2457, hlam]

end R2N4
