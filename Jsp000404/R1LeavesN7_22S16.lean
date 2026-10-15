import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 5 (by decide) (by decide) with h1873 | h1873
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1874 | h1874
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1875 | h1875
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1876 | h1876
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1877 | h1877
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1878 | h1878
            · linarith only [h1873, h1878, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1880 | h1880
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1881 | h1881
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1882 | h1882
                  · linarith only [h1, h1880, h1882, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1884 | h1884
                    · linarith only [h0, h1876, h1882, h1884, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h1, h1880, h1884, h7, hc23, hc34, hlam, hphi]
                · linarith only [h1874, h1878, h1880, h1881, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h1873, h1880, h7, hc13, hc34, hlam, hphi]
          · linarith only [h1873, h1875, h1877, h6, h7, hc23, hc34, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1890 | h1890
          · linarith only [h0, h1876, h1890, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · linarith only [h1873, h1875, h1890, h6, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1893 | h1893
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1894 | h1894
          · linarith only [h0, h1875, h1894, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1896 | h1896
            · linarith only [h1873, h1893, h1894, h1896, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h1875, h1893, h1896, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1899 | h1899
          · linarith only [h1875, h1899, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1901 | h1901
            · linarith only [h1901, h7, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1903 | h1903
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1904 | h1904
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1905 | h1905
                  · linarith only [h1905, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1907 | h1907
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1908 | h1908
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1909 | h1909
                        · rcases h2bigk with h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            rcases p1910_3 (m.d 0 2) (by simp) with h1912 | h1912
                            · rcases p1910_3 (m.d 1 2) (by simp) with h1913 | h1913
                              · linarith only [h0, h1913, hlam]
                              · rcases p1910_3 (m.d 2 3) (by simp) with h1915 | h1915
                                · linarith only [h1915, h4, hlam]
                                · linarith only [h1875, h1915, hlam]
                            · linarith only [h0, h1912, hlam]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h1875, h1903, h1909, hc02, hlam, hphi, ht0b, ht5b, p1910_1, u5ehi4]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h0, h1893, h1901, h1903, h1909, hc01, hlam, hphi, ht0b, ht5b, p1910_1, u5ehi4]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            rcases p1910_3 (m.d 0 2) (by simp) with h1921 | h1921
                            · rcases p1910_3 (m.d 1 2) (by simp) with h1922 | h1922
                              · linarith only [h0, h1922, hlam]
                              · rcases p1910_3 (m.d 2 3) (by simp) with h1924 | h1924
                                · linarith only [h1924, h4, hlam]
                                · linarith only [h1907, h1924, hlam]
                            · linarith only [h1921, hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h0, hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h1875, hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h1893, hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h1899, hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h4, hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p1910_1]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h1905, hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h1899, h4, h7, hc12, hc34, hlam, hphi, ht23, p1910_1]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h5, hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            rcases p1910_3 (m.d 0 2) (by simp) with h1939 | h1939
                            · rcases p1910_3 (m.d 1 2) (by simp) with h1940 | h1940
                              · linarith only [h1940, hlam, p1910_0]
                              · rcases p1910_3 (m.d 2 3) (by simp) with h1942 | h1942
                                · linarith only [h1905, h1942, hlam]
                                · linarith only [h1875, h1942, hlam]
                            · linarith only [h0, h1939, hlam]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h1875, h1903, h1909, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1910_1, u5ehi4]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h0, h1875, h1899, h1903, h1909, h4, h5, h7, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht5b, p1910_1, u5ehi4]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h6, hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h1873, h6, h7, hc12, hc34, hlam, hphi, ht23, p1910_1]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h1907, hlam, p1910_1]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [h1908, hlam, p1910_0]
                          · have p1910_0 := h1910c.1
                            have p1910_1 := h1910c.2.1
                            have p1910_2 := h1910c.2.2.1
                            have p1910_3 := h1910c.2.2.2
                            linarith only [hlam, p1910_0]
                        · linarith only [h1875, h1903, h1909, h4, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                      · linarith only [h1873, h1874, h1893, h1908, h7, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1875, h1903, h1907, hlam]
                · linarith only [h1874, h1901, h1903, h1904, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · linarith only [h1873, h1903, h7, hc13, hc34, hlam, hphi]
    · linarith only [h1873, h1874, h7, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1960 | h1960
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1961 | h1961
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1962 | h1962
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1963 | h1963
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1964 | h1964
            · linarith only [h1, h1964, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1966 | h1966
              · linarith only [h1873, h1966, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1968 | h1968
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1969 | h1969
                  · linarith only [h1, h1873, h1961, h1969, h7, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1971 | h1971
                    · linarith only [h0, h1873, h1962, h1969, h1971, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1973 | h1973
                      · linarith only [h0, h1962, h1973, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1975 | h1975
                        · rcases h2bigk with h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h1962, h1968, h1969, h1973, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1976_1]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            rcases p1976_3 (m.d 0 2) (by simp) with h1979 | h1979
                            · rcases p1976_3 (m.d 1 2) (by simp) with h1980 | h1980
                              · linarith only [h0, h1980, hlam]
                              · linarith only [h1961, h1980, hlam]
                            · linarith only [h1979, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            rcases p1976_3 (m.d 0 2) (by simp) with h1984 | h1984
                            · rcases p1976_3 (m.d 1 2) (by simp) with h1985 | h1985
                              · linarith only [h0, h1985, hlam]
                              · linarith only [h1962, h1985, hlam]
                            · linarith only [h1984, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            rcases p1976_3 (m.d 0 2) (by simp) with h1989 | h1989
                            · rcases p1976_3 (m.d 1 2) (by simp) with h1990 | h1990
                              · linarith only [h0, h1990, hlam]
                              · linarith only [h1963, h1990, hlam]
                            · linarith only [h1989, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h0, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            rcases p1976_3 (m.d 0 2) (by simp) with h1996 | h1996
                            · rcases p1976_3 (m.d 1 2) (by simp) with h1997 | h1997
                              · rcases p1976_3 (m.d 2 3) (by simp) with h1998 | h1998
                                · linarith only [h1998, hlam, p1976_0]
                                · rcases p1976_3 (m.d 2 4) (by simp) with h2000 | h2000
                                  · linarith only [h1962, h2000, hlam]
                                  · linarith only [h1969, h2000, hlam]
                              · linarith only [h1997, hlam, p1976_0]
                            · linarith only [h1996, h4, hlam]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            rcases p1976_3 (m.d 0 2) (by simp) with h2005 | h2005
                            · rcases p1976_3 (m.d 1 2) (by simp) with h2006 | h2006
                              · rcases p1976_3 (m.d 2 3) (by simp) with h2007 | h2007
                                · linarith only [h1961, h2007, hlam]
                                · rcases p1976_3 (m.d 2 4) (by simp) with h2009 | h2009
                                  · linarith only [h2009, hlam, p1976_0]
                                  · rcases p1976_3 (m.d 2 5) (by simp) with h2011 | h2011
                                    · linarith only [h1963, h2011, hlam]
                                    · linarith only [h1973, h2011, hlam]
                              · linarith only [h2006, hlam, p1976_0]
                            · linarith only [h2005, h5, hlam]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1976_1, u5ehi2]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h4, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h1961, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h1969, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h1971, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h5, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h1962, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h1968, h1973, h2, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1976_1]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h1973, hlam, p1976_1]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h6, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h1963, hlam, p1976_0]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h0, h1963, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1976_1]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [h0, h1962, h1968, h1973, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1976_1]
                          · have p1976_0 := h1976c.1
                            have p1976_1 := h1976c.2.1
                            have p1976_2 := h1976c.2.2.1
                            have p1976_3 := h1976c.2.2.2
                            linarith only [hlam, p1976_0]
                        · linarith only [h0, h1962, h1968, h1975, h7, hc01, hlam, hphi, u0ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2033 | h2033
                  · linarith only [h1960, h1961, h1964, h1968, h2033, h7, hc04, hlam, hphi, u0ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2035 | h2035
                    · linarith only [h1873, h2035, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2037 | h2037
                      · linarith only [h1962, h1968, h2037, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2039 | h2039
                        · rcases h2bigk with h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h0, h1963, hc01, hlam, hphi, ht0b, ht5b, p2040_1, u5ehi2]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            rcases p2040_3 (m.d 0 2) (by simp) with h2043 | h2043
                            · rcases p2040_3 (m.d 1 2) (by simp) with h2044 | h2044
                              · linarith only [h0, h2044, hlam]
                              · linarith only [h1961, h2044, hlam]
                            · linarith only [h2043, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            rcases p2040_3 (m.d 0 2) (by simp) with h2048 | h2048
                            · rcases p2040_3 (m.d 1 2) (by simp) with h2049 | h2049
                              · linarith only [h0, h2049, hlam]
                              · linarith only [h1962, h2049, hlam]
                            · linarith only [h2048, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            rcases p2040_3 (m.d 0 2) (by simp) with h2053 | h2053
                            · rcases p2040_3 (m.d 1 2) (by simp) with h2054 | h2054
                              · linarith only [h0, h2054, hlam]
                              · linarith only [h1963, h2054, hlam]
                            · linarith only [h2053, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h0, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            rcases p2040_3 (m.d 0 2) (by simp) with h2060 | h2060
                            · rcases p2040_3 (m.d 1 2) (by simp) with h2061 | h2061
                              · rcases p2040_3 (m.d 2 3) (by simp) with h2062 | h2062
                                · linarith only [h2062, hlam, p2040_0]
                                · rcases p2040_3 (m.d 2 4) (by simp) with h2064 | h2064
                                  · linarith only [h1962, h2064, hlam]
                                  · linarith only [h2033, h2064, hlam]
                              · linarith only [h2061, hlam, p2040_0]
                            · linarith only [h2060, h4, hlam]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            rcases p2040_3 (m.d 0 2) (by simp) with h2069 | h2069
                            · rcases p2040_3 (m.d 1 2) (by simp) with h2070 | h2070
                              · rcases p2040_3 (m.d 2 3) (by simp) with h2071 | h2071
                                · linarith only [h1961, h2071, hlam]
                                · rcases p2040_3 (m.d 2 4) (by simp) with h2073 | h2073
                                  · linarith only [h2073, hlam, p2040_0]
                                  · rcases p2040_3 (m.d 2 5) (by simp) with h2075 | h2075
                                    · linarith only [h1963, h2075, hlam]
                                    · linarith only [h2037, h2075, hlam]
                              · linarith only [h2070, hlam, p2040_0]
                            · linarith only [h2069, h5, hlam]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p2040_1, u5ehi2]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h4, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h1961, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h2033, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h2035, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h5, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h1962, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h0, h1962, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2040_1]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h2037, hlam, p2040_1]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h6, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h1963, hlam, p2040_0]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h0, h1963, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2040_1]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [h0, h1963, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2040_1]
                          · have p2040_0 := h2040c.1
                            have p2040_1 := h2040c.2.1
                            have p2040_2 := h2040c.2.2.1
                            have p2040_3 := h2040c.2.2.2
                            linarith only [hlam, p2040_0]
                        · linarith only [h1960, h2039, h7, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2097 | h2097
            · linarith only [h1, h1960, h2097, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2099 | h2099
              · linarith only [h0, h1873, h1962, h1963, h2097, h2099, h6, hc01, hlam, hphi, u0ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2101 | h2101
                · linarith only [h0, h1962, h1963, h2101, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2103 | h2103
                  · linarith only [h0, h1960, h2097, h2101, h2103, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2105 | h2105
                    · linarith only [h1873, h1961, h2105, hc13, hlam, hphi, ht01, u0ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2107 | h2107
                      · linarith only [h0, h1962, h1963, h2097, h2101, h2107, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1960, h1962, h1963, h2103, h2107, h7, hc23, hc34, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2110 | h2110
          · linarith only [h0, h1962, h2110, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2112 | h2112
            · linarith only [h2112, h7, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2114 | h2114
              · linarith only [h0, h1961, h2110, h2114, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2116 | h2116
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2117 | h2117
                  · linarith only [h2117, h7, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2119 | h2119
                    · linarith only [h0, h1873, h1961, h2110, h2119, h6, hc01, hlam, hphi, u0ehi2]
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
                                  · linarith only [h1962, h2130, hlam]
                            · linarith only [h0, h2125, hlam]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h1961, h2110, h2121, h5, hlam, p2123_2]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, h1961, h2110, h2121, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2123_1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, h1961, h2110, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2123_1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, h2110, h2121, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2123_1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h1962, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h2110, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h4, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h1961, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h2117, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h2119, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h5, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, h1961, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2123_1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            rcases p2123_3 (m.d 0 2) (by simp) with h2149 | h2149
                            · rcases p2123_3 (m.d 1 2) (by simp) with h2150 | h2150
                              · linarith only [h1962, h2150, hlam]
                              · linarith only [h1961, h2150, hlam]
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
                            linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht5b, p2123_1, u5ehi2]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h6, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, h1961, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2123_1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            rcases p2123_3 (m.d 0 2) (by simp) with h2158 | h2158
                            · rcases p2123_3 (m.d 1 2) (by simp) with h2159 | h2159
                              · linarith only [h2110, h2159, hlam]
                              · linarith only [h1961, h2159, hlam]
                            · linarith only [h2158, h4, hlam]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h2121, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [hlam, p2123_0]
                        · linarith only [h2116, h2122, h7, hc14, hlam, hphi, ht01, u0ehi2]
                      · linarith only [h1960, h1961, h1962, h2121, h7, hc23, hc34, hlam, hphi]
                · linarith only [h1960, h1961, h1962, h2116, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2168 | h2168
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2169 | h2169
          · linarith only [h1873, h1961, h2169, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2171 | h2171
            · linarith only [h1, h1960, h2171, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · linarith only [h1961, h2168, h2171, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2174 | h2174
          · linarith only [h1873, h1961, h2174, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2176 | h2176
            · linarith only [h2176, h7, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2178 | h2178
              · linarith only [h1873, h2178, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2180 | h2180
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2181 | h2181
                  · linarith only [h2181, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2183 | h2183
                    · linarith only [h1873, h2183, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2185 | h2185
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2186 | h2186
                        · rcases h2bigk with h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c | h2187c
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            rcases p2187_3 (m.d 0 2) (by simp) with h2189 | h2189
                            · rcases p2187_3 (m.d 1 2) (by simp) with h2190 | h2190
                              · linarith only [h0, h2190, hlam]
                              · rcases p2187_3 (m.d 2 3) (by simp) with h2192 | h2192
                                · linarith only [h2192, h4, hlam]
                                · linarith only [h1961, h2192, hlam]
                            · linarith only [h0, h2189, hlam]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            rcases p2187_3 (m.d 0 2) (by simp) with h2196 | h2196
                            · rcases p2187_3 (m.d 1 2) (by simp) with h2197 | h2197
                              · linarith only [h0, h2197, hlam]
                              · rcases p2187_3 (m.d 2 3) (by simp) with h2199 | h2199
                                · linarith only [h2199, hlam, p2187_0]
                                · rcases p2187_3 (m.d 2 4) (by simp) with h2201 | h2201
                                  · linarith only [h2201, h5, hlam]
                                  · linarith only [h2181, h2201, hlam]
                            · linarith only [h2196, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h0, h2168, h2180, hc01, hlam, hphi, ht0b, ht5b, p2187_1, u5ehi4]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            rcases p2187_3 (m.d 0 2) (by simp) with h2206 | h2206
                            · rcases p2187_3 (m.d 1 2) (by simp) with h2207 | h2207
                              · linarith only [h0, h2207, hlam]
                              · rcases p2187_3 (m.d 2 3) (by simp) with h2209 | h2209
                                · linarith only [h2209, h4, hlam]
                                · rcases p2187_3 (m.d 2 4) (by simp) with h2211 | h2211
                                  · linarith only [h2211, h5, hlam]
                                  · linarith only [h2185, h2211, hlam]
                            · linarith only [h2206, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h0, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h1961, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h2168, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h2174, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h4, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h1873, h2186, h4, hc12, hc34, hlam, hphi, ht23, p2187_1]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h2181, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h2183, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h5, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            rcases p2187_3 (m.d 0 2) (by simp) with h2226 | h2226
                            · rcases p2187_3 (m.d 1 2) (by simp) with h2227 | h2227
                              · linarith only [h2227, hlam, p2187_0]
                              · rcases p2187_3 (m.d 2 3) (by simp) with h2229 | h2229
                                · linarith only [h2181, h2229, hlam]
                                · linarith only [h1961, h2229, hlam]
                            · linarith only [h0, h2226, hlam]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h1961, hc12, hc24, hlam, hphi, p2187_1]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h0, h2174, h5, hc01, hlam, hphi, ht0b, ht5b, p2187_1, u5ehi1]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h6, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            rcases p2187_3 (m.d 0 2) (by simp) with h2237 | h2237
                            · rcases p2187_3 (m.d 1 2) (by simp) with h2238 | h2238
                              · linarith only [h2238, hlam, p2187_0]
                              · rcases p2187_3 (m.d 2 3) (by simp) with h2240 | h2240
                                · linarith only [h2183, h2240, hlam]
                                · linarith only [h1961, h2240, hlam]
                            · linarith only [h0, h2237, hlam]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h1961, hc12, hc25, hlam, hphi, p2187_1]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [h2185, hlam, p2187_0]
                          · have p2187_0 := h2187c.1
                            have p2187_1 := h2187c.2.1
                            have p2187_2 := h2187c.2.2.1
                            have p2187_3 := h2187c.2.2.2
                            linarith only [hlam, p2187_0]
                        · linarith only [h2, h2180, h2186, h7, hc01, hlam, hphi, u0ehi2]
                      · linarith only [h1960, h2168, h2185, h7, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2249 | h2249
                  · linarith only [h0, h1960, h2176, h2180, h2249, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2251 | h2251
                    · linarith only [h1873, h2251, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2253 | h2253
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2254 | h2254
                        · rcases h2bigk with h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c | h2255c
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h1961, h2176, h2180, h2253, h5, hlam, p2255_2]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            rcases p2255_3 (m.d 0 2) (by simp) with h2258 | h2258
                            · rcases p2255_3 (m.d 1 2) (by simp) with h2259 | h2259
                              · linarith only [h0, h2259, hlam]
                              · rcases p2255_3 (m.d 2 3) (by simp) with h2261 | h2261
                                · linarith only [h2261, hlam, p2255_0]
                                · rcases p2255_3 (m.d 2 4) (by simp) with h2263 | h2263
                                  · linarith only [h2263, h5, hlam]
                                  · linarith only [h2249, h2263, hlam]
                            · linarith only [h2258, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h0, h1961, h2176, h2180, h2253, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2255_1]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            rcases p2255_3 (m.d 0 2) (by simp) with h2268 | h2268
                            · rcases p2255_3 (m.d 1 2) (by simp) with h2269 | h2269
                              · linarith only [h0, h2269, hlam]
                              · rcases p2255_3 (m.d 2 3) (by simp) with h2271 | h2271
                                · linarith only [h2271, h4, hlam]
                                · rcases p2255_3 (m.d 2 4) (by simp) with h2273 | h2273
                                  · linarith only [h2273, h5, hlam]
                                  · linarith only [h2253, h2273, hlam]
                            · linarith only [h2268, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h0, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h1961, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h2168, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h2174, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h4, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h1873, h2254, h4, hc12, hc34, hlam, hphi, ht23, p2255_1]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h2249, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h2251, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h5, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            rcases p2255_3 (m.d 0 2) (by simp) with h2288 | h2288
                            · rcases p2255_3 (m.d 1 2) (by simp) with h2289 | h2289
                              · linarith only [h2289, hlam, p2255_0]
                              · rcases p2255_3 (m.d 2 3) (by simp) with h2291 | h2291
                                · linarith only [h2249, h2291, hlam]
                                · linarith only [h1961, h2291, hlam]
                            · linarith only [h0, h2288, hlam]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h1961, hc12, hc24, hlam, hphi, p2255_1]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h0, h2174, h5, hc01, hlam, hphi, ht0b, ht5b, p2255_1, u5ehi1]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h6, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            rcases p2255_3 (m.d 0 2) (by simp) with h2299 | h2299
                            · rcases p2255_3 (m.d 1 2) (by simp) with h2300 | h2300
                              · linarith only [h2300, hlam, p2255_0]
                              · rcases p2255_3 (m.d 2 3) (by simp) with h2302 | h2302
                                · linarith only [h2251, h2302, hlam]
                                · linarith only [h1961, h2302, hlam]
                            · linarith only [h0, h2299, hlam]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h1961, hc12, hc25, hlam, hphi, p2255_1]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [h2253, hlam, p2255_0]
                          · have p2255_0 := h2255c.1
                            have p2255_1 := h2255c.2.1
                            have p2255_2 := h2255c.2.2.1
                            have p2255_3 := h2255c.2.2.2
                            linarith only [hlam, p2255_0]
                        · linarith only [h2254, h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                      · linarith only [h1960, h2168, h2253, h7, hc12, hc34, hlam, hphi, ht23]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2311 | h2311
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2312 | h2312
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2313 | h2313
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2314 | h2314
            · linarith only [h2314, h7, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2316 | h2316
              · linarith only [h1, h1873, h2316, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2318 | h2318
                · linarith only [h1960, h2318, hc14, hlam, hphi, ht01, u0ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2320 | h2320
                  · linarith only [h1, h2311, h2320, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2322 | h2322
                    · linarith only [h1, h1873, h2311, h2322, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2324 | h2324
                      · linarith only [h0, h1960, h2312, h2324, h7, hc01, hlam, hphi, u0ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2326 | h2326
                        · linarith only [h1960, h2326, h7, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2326, h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2329 | h2329
            · linarith only [h0, h2311, h2313, h2329, h6, h7, hc01, hlam, hphi, u0ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2331 | h2331
              · linarith only [h0, h1873, h2312, h2313, h2329, h2331, h6, hc01, hlam, hphi, u0ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2333 | h2333
                · linarith only [h0, h2312, h2313, h2333, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2335 | h2335
                  · linarith only [h0, h2311, h2313, h2335, h6, h7, hc01, hlam, hphi, u0ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2337 | h2337
                    · linarith only [h0, h1873, h2312, h2313, h2335, h2337, h6, hc01, hlam, hphi, u0ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2339 | h2339
                      · linarith only [h0, h1960, h2312, h2313, h2339, h6, h7, hc01, hlam, hphi, u0ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2341 | h2341
                        · linarith only [h1960, h2341, h7, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2341, h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
        · linarith only [h1960, h2311, h2312, h5, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2345 | h2345
        · linarith only [h1960, h2311, h2345, h4, h7, hc24, hc45, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2347 | h2347
          · linarith only [h1960, h2311, h2347, h4, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2349 | h2349
            · linarith only [h2349, h7, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2351 | h2351
              · linarith only [h1873, h2351, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2353 | h2353
                · linarith only [h1960, h2345, h2353, h5, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2355 | h2355
                  · linarith only [h2355, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2357 | h2357
                    · linarith only [h1873, h2357, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2359 | h2359
                      · linarith only [h1960, h2359, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2361 | h2361
                        · linarith only [h1960, h2361, h7, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h2361, h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]

set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7

set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h2364 | h2364
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2365 | h2365
    · linarith only [h2365, h4, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2367 | h2367
      · linarith only [h2367, h5, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2369 | h2369
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2370 | h2370
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2371 | h2371
            · linarith only [h2371, h6, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2373 | h2373
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2374 | h2374
                · linarith only [h0, h2364, h2365, h2369, h2374, hc02, hlam, hphi, u0ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2376 | h2376
                  · linarith only [h2, h2367, h2376, hc01, hlam, hphi, u0ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2378 | h2378
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2379 | h2379
                      · linarith only [h0, h2369, h2379, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2381 | h2381
                        · linarith only [h0, h2367, h2369, h2378, h2379, h2381, h6, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h2369, h2378, h2381, h6, hc34, hc45, hlam, hphi]
                    · linarith only [h2364, h2365, h2378, hc23, hc35, hlam, hphi]
              · linarith only [h2364, h2365, h2373, hc13, hc35, hlam, hphi]
          · linarith only [h2370, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h2369, h4, h6, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2388 | h2388
    · linarith only [h2388, h4, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2390 | h2390
      · linarith only [h2390, h5, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2392 | h2392
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2393 | h2393
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2394 | h2394
            · linarith only [h2394, h6, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2396 | h2396
              · linarith only [h2364, h2396, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2398 | h2398
                · linarith only [h2388, h2398, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2400 | h2400
                  · linarith only [h2, h2390, h2400, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2402 | h2402
                    · linarith only [h2364, h2402, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2404 | h2404
                      · linarith only [h0, h2388, h2393, h2402, h2404, hc02, hlam, hphi, u0ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2406 | h2406
                        · linarith only [h0, h2390, h2393, h2404, h2406, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2408 | h2408
                          · linarith only [h0, h2393, h2402, h2406, h2408, h6, hc23, hc34, hlam, hphi]
                          · linarith only [h2364, h2408, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
          · linarith only [h2393, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h2392, h4, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6

set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 5 (by decide) (by decide) with h2413 | h2413
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2414 | h2414
    · linarith only [h2414, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2416 | h2416
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2417 | h2417
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2418 | h2418
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2419 | h2419
            · linarith only [h0, h2419, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2421 | h2421
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2422 | h2422
                · linarith only [h1, h2414, h2422, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2424 | h2424
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2425 | h2425
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2426 | h2426
                      · linarith only [h0, h2414, h2418, h2426, h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2428 | h2428
                        · linarith only [h0, h2418, h2426, h2428, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h1, h2424, h2426, h2428, h4, h5, hc23, hc34, hlam, hphi]
                    · linarith only [h2414, h2416, h2417, h2418, h2419, h2425, hc23, hc34, hlam, hphi]
                  · linarith only [h2414, h2416, h2424, hc13, hc34, hlam, hphi]
              · linarith only [h2413, h2421, h5, hc12, hc24, hlam, hphi]
          · linarith only [h2418, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h2416, h2417, h4, h5, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2436 | h2436
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2437 | h2437
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2438 | h2438
            · linarith only [h0, h2438, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2440 | h2440
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2441 | h2441
                · linarith only [h2414, h2441, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2443 | h2443
                  · linarith only [h1, h2416, h2443, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2445 | h2445
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2446 | h2446
                      · linarith only [h0, h2414, h2437, h2446, hc02, hlam, hphi, u0ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2448 | h2448
                        · linarith only [h0, h2416, h2437, h2446, h2448, h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2450 | h2450
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2451 | h2451
                            · rcases h2bigk with h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c | h2452c
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2446, h5, hc12, hc34, hlam, hphi, ht23, p2452_1]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2446, h5, hc23, hc34, hlam, hphi, p2452_1]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h5, hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2446, h2450, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2452_1, u5ehi4]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h0, hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h0, h2446, h5, hc23, hc34, hlam, hphi, p2452_1]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2438, hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h0, h2446, h2450, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2452_1, u5ehi4]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h4, hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2437, hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2446, hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2448, hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2446, hc34, hlam, hphi, ht01, ht12, ht23, p2452_1, u0ehi1]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2437, h2446, hc23, hc34, hlam, hphi, p2452_1]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                rcases p2452_3 (m.d 0 2) (by simp) with h2470 | h2470
                                · linarith only [h2470, h5, hlam]
                                · linarith only [h2470, h4, hlam]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                rcases p2452_3 (m.d 0 2) (by simp) with h2474 | h2474
                                · linarith only [h2474, h5, hlam]
                                · linarith only [h2413, h2474, hlam]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2413, hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2440, hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h0, h2440, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2452_1]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [h2450, hlam, p2452_0]
                              · have p2452_0 := h2452c.1
                                have p2452_1 := h2452c.2.1
                                have p2452_2 := h2452c.2.2.1
                                have p2452_3 := h2452c.2.2.2
                                linarith only [hlam, p2452_0]
                            · linarith only [h0, h2440, h2446, h2450, h2451, h5, hlam]
                          · linarith only [h0, h2440, h2450, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · linarith only [h2414, h2436, h2438, h2440, h2445, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
              · linarith only [h2413, h2440, h5, hc12, hc24, hlam, hphi]
          · linarith only [h2437, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h2413, h2436, h5, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2488 | h2488
    · linarith only [h2488, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2490 | h2490
      · linarith only [h2413, h2490, h4, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2492 | h2492
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2493 | h2493
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2494 | h2494
            · linarith only [h2494, h5, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2496 | h2496
              · linarith only [h2413, h2496, h4, hc12, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2498 | h2498
                · linarith only [h1, h2488, h2492, h2498, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2500 | h2500
                  · linarith only [h1, h2490, h2500, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2502 | h2502
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2503 | h2503
                      · linarith only [h0, h2413, h2488, h2493, h2503, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2505 | h2505
                        · linarith only [h2490, h2493, h2505, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2507 | h2507
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2508 | h2508
                            · rcases h2bigk with h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2413, h2503, h2507, hc12, hc34, hlam, hphi, ht23, p2509_1]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2413, h2503, h2507, hc23, hc34, hlam, hphi, p2509_1]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h5, hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2413, hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h0, hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h0, h2413, h2503, h2507, hc23, hc34, hlam, hphi, p2509_1]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2494, hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2496, hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h4, hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2493, hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2503, hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2505, hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2503, hc34, hlam, hphi, ht01, ht12, ht23, p2509_1, u0ehi1]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2493, h2503, hc23, hc34, hlam, hphi, p2509_1]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                rcases p2509_3 (m.d 0 2) (by simp) with h2527 | h2527
                                · linarith only [h2527, h5, hlam]
                                · linarith only [h2527, h4, hlam]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2413, h2503, h4, hc34, hlam, hphi, ht01, ht12, ht23, p2509_1, u0ehi2]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h4, hc25, hlam, hphi, ht01, ht12, p2509_1, u0ehi2]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2493, h2505, h2508, hc23, hc34, hlam, hphi, p2509_1]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                rcases p2509_3 (m.d 0 2) (by simp) with h2534 | h2534
                                · linarith only [h2413, h2534, hlam]
                                · linarith only [h2534, h4, hlam]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [h2507, hlam, p2509_0]
                              · have p2509_0 := h2509c.1
                                have p2509_1 := h2509c.2.1
                                have p2509_2 := h2509c.2.2.1
                                have p2509_3 := h2509c.2.2.2
                                linarith only [hlam, p2509_0]
                            · linarith only [h2503, h2508, h4, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                          · linarith only [h2, h2502, h2507, h4, h5, hc04, hlam, hphi, u0ehi2]
                    · linarith only [h2488, h2492, h2493, h2494, h2502, hc23, hc34, hlam, hphi]
          · linarith only [h2493, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2543 | h2543
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2544 | h2544
            · linarith only [h2544, h5, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2546 | h2546
              · linarith only [h0, h2413, h2546, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2548 | h2548
                · linarith only [h2488, h2548, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2550 | h2550
                  · linarith only [h1, h2490, h2550, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2552 | h2552
                    · linarith only [h2492, h2552, hc14, hlam, hphi, ht01, u0ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2554 | h2554
                      · linarith only [h2488, h2554, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2556 | h2556
                        · linarith only [h0, h2490, h2492, h2543, h2556, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2558 | h2558
                          · linarith only [h0, h2492, h2543, h2554, h2558, h5, hc23, hc34, hlam, hphi]
                          · linarith only [h2558, h4, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
          · linarith only [h2543, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5

end R2N4
