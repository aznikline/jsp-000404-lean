import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_51S15
import Jsp000404.R1LeavesN7_51S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5286000 in
set_option maxHeartbeats 5286000 in
theorem r1l7_20_12_14_M_LI_L_I_L_0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1079 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1478 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h1871 | h1871
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1872 | h1872
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1873 | h1873
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1874 | h1874
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1875 | h1875
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1876 | h1876
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1877 | h1877
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1878 | h1878
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1879 | h1879
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1880 | h1880
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1881 | h1881
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1882 | h1882
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1883 | h1883
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1884 | h1884
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1885 | h1885
                              · linarith only [h1872, h1882, h1885, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h1877, h1885, hc34, hlam, hphi, u4elo0]
                            · linarith only [h1478, h1871, h1881, h1884, hc24, hlam, hphi, u4elo1]
                          · linarith only [h1478, h1871, h1876, h1883, hc23, hlam, hphi, ht34, u4elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1890 | h1890
                          · linarith only [h1872, h1875, h1882, h1890, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h1478, h1871, h1876, h1890, hc23, hlam, hphi, ht34, u4elo1]
                      · linarith only [h1478, h1881, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h1874, h1880, hlam]
                  · linarith only [h0, h1872, h1875, h1879, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h1872, h1878, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1478, h1871, h1877, hlam]
            · linarith only [h1478, h1871, h1875, h1876, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1899 | h1899
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1900 | h1900
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1901 | h1901
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1902 | h1902
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1903 | h1903
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1904 | h1904
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1905 | h1905
                        · linarith only [h1872, h1875, h1905, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1907 | h1907
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1908 | h1908
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1909 | h1909
                              · rcases h0bigk with h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [hlam, p1910_0]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h0, hlam, p1910_1]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1079, hlam, p1910_0]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1478, hlam, p1910_1]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1079, h1875, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1910_1, u4elo3]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1871, hc15, hlam, hphi, ht0b, ht5b, p1910_1, u0elo1]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [hlam, p1910_0]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1079, h1871, h1903, h1907, h1909, hc45, hlam, hphi, ht0b, ht5b, p1910_1, u0elo1]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1478, h1871, h1903, h1907, h1909, hc45, hlam, hphi, ht0b, ht5b, p1910_1, u0elo1]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  rcases p1910_3 (m.d 0 1) (by simp) with h1920 | h1920
                                  · linarith only [h0, h1920, hlam]
                                  · linarith only [h1871, h1920, hlam]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1871, h1903, h1907, h1909, hc45, hlam, hphi, ht0b, ht5b, p1910_1, u0elo2]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1872, hlam, p1910_1]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [hlam, p1910_0]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1875, hlam, p1910_1]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1871, h1875, h1903, h1907, h1909, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1910_1, u4elo3]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1871, h1903, h1907, h1909, hc45, hlam, hphi, ht0b, ht5b, p1910_1, u0elo3]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1873, hlam, p1910_0]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1478, hc03, hlam, hphi, ht34, p1910_1, u4elo1]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [hlam, p1910_0]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  rcases p1910_3 (m.d 0 1) (by simp) with h1932 | h1932
                                  · linarith only [h1478, h1932, hlam]
                                  · linarith only [h1871, h1932, hlam]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1871, hlam, p1910_0]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1874, hlam, p1910_1]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1899, hlam, p1910_0]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [h1900, hlam, p1910_1]
                                · have p1910_0 := h1910c.1
                                  have p1910_1 := h1910c.2.1
                                  have p1910_2 := h1910c.2.2.1
                                  have p1910_3 := h1910c.2.2.2
                                  linarith only [hlam, p1910_0]
                              · linarith only [h1079, h1871, h1875, h1903, h1907, h1909, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h1478, h1871, h1904, h1908, hc24, hlam, hphi, u4elo1]
                          · linarith only [h1875, h1899, h1907, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h1478, h1871, h1904, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h0, h1874, h1903, hlam]
                  · linarith only [h0, h1871, h1902, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                · linarith only [h0, h1872, h1901, hlam]
              · linarith only [h1478, h1871, h1900, hlam]
            · linarith only [h1079, h1871, h1899, hlam]
        · linarith only [h1478, h1871, h1872, h1874, hc23, hlam, hphi, ht34, u4elo1]
      · linarith only [h1872, h1873, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1951 | h1951
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1952 | h1952
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1953 | h1953
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1954 | h1954
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1955 | h1955
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1956 | h1956
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1957 | h1957
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1958 | h1958
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1959 | h1959
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1960 | h1960
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1961 | h1961
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1962 | h1962
                            · linarith only [h1872, h1951, h1956, h1962, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1872, h1951, h1955, h1956, h1962, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1478, h1871, h1872, h1954, h1958, h1961, hc02, hc25, hlam, hphi, ht0b, ht23, ht34, ht5b, u0elo2, u4elo1]
                        · linarith only [h1872, h1951, h1960, hc24, hlam, hphi, u4elo3]
                      · linarith only [h1478, h1871, h1958, h1959, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h1872, h1952, h1958, hc12, hc23, hlam, hphi]
                  · linarith only [h1872, h1956, h1957, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1970 | h1970
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1971 | h1971
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1972 | h1972
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1973 | h1973
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1974 | h1974
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1975 | h1975
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1976 | h1976
                              · rcases h0bigk with h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [hlam, p1977_0]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h0, hlam, p1977_1]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1079, hlam, p1977_0]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1478, hlam, p1977_1]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1478, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1977_1, u4elo1]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1871, h1872, hc15, hlam, hphi, ht0b, ht5b, p1977_1, u0elo2]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [hlam, p1977_0]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1872, hlam, p1977_0]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h0, h1478, h1871, h1956, h1971, h1974, h1976, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1977_1]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  rcases p1977_3 (m.d 0 1) (by simp) with h1987 | h1987
                                  · linarith only [h0, h1987, hlam]
                                  · linarith only [h1871, h1987, hlam]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1871, h1971, h1974, h1976, hc45, hlam, hphi, ht0b, ht5b, p1977_1, u0elo2]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h0, h1871, h1971, h1974, h1976, hc45, hlam, hphi, ht0b, ht5b, p1977_1, u0elo2]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [hlam, p1977_0]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1478, h1871, h1971, h1974, h1976, hc45, hlam, hphi, ht0b, ht5b, p1977_1, u0elo2]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  rcases p1977_3 (m.d 0 1) (by simp) with h1994 | h1994
                                  · linarith only [h1079, h1994, hlam]
                                  · linarith only [h1871, h1994, hlam]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1871, h1971, h1974, h1976, hc45, hlam, hphi, ht0b, ht5b, p1977_1, u0elo3]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1951, hlam, p1977_0]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1953, hlam, p1977_0]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [hlam, p1977_0]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  rcases p1977_3 (m.d 0 1) (by simp) with h2001 | h2001
                                  · linarith only [h1478, h2001, hlam]
                                  · linarith only [h1871, h2001, hlam]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1871, hlam, p1977_0]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1952, hlam, p1977_1]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1954, hlam, p1977_0]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [h1955, hlam, p1977_1]
                                · have p1977_0 := h1977c.1
                                  have p1977_1 := h1977c.2.1
                                  have p1977_2 := h1977c.2.2.1
                                  have p1977_3 := h1977c.2.2.2
                                  linarith only [hlam, p1977_0]
                              · linarith only [h1478, h1955, h1976, hc34, hlam, hphi, u4elo1]
                            · linarith only [h0, h1871, h1956, h1972, h1973, h1975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h1871, h1956, h1972, h1974, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h1956, h1973, hc02, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h1478, h1871, h1971, h1972, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h1478, h1952, h1970, h1971, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1871, h1970, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h1478, h1871, h1955, hlam]
            · linarith only [h1079, h1871, h1954, hlam]
          · linarith only [h1872, h1951, h1953, hc24, hlam, hphi, u4elo3]
        · linarith only [h1478, h1871, h1951, h1952, hc24, hlam, hphi, u4elo1]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2020 | h2020
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2021 | h2021
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2022 | h2022
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2023 | h2023
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2024 | h2024
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2025 | h2025
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2026 | h2026
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2027 | h2027
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2028 | h2028
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2029 | h2029
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2030 | h2030
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2031 | h2031
                              · rcases h0bigk with h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c | h2032c
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [hlam, p2032_0]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h0, hlam, p2032_1]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h1079, hlam, p2032_0]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h1478, hlam, p2032_1]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h0, h1951, h2025, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2032_1, u4elo1]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h1951, h2025, hc01, hlam, hphi, ht12, ht23, ht34, p2032_1, u4elo1]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [hlam, p2032_0]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h1872, hlam, p2032_0]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h1951, hlam, p2032_1]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h1871, h1951, h2025, h2026, h2029, h2031, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2032_1, u4elo1]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h1871, h2026, h2029, h2031, hc45, hlam, hphi, ht0b, ht5b, p2032_1, u0elo2]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h0, h1871, h1872, h2024, h2026, h2029, h2031, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2032_1]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [hlam, p2032_0]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h0, h1871, h1872, h1951, h2024, h2026, h2029, h2031, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2032_1]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  rcases p2032_3 (m.d 0 1) (by simp) with h2047 | h2047
                                  · linarith only [h1079, h2047, hlam]
                                  · linarith only [h1871, h2047, hlam]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h1871, h2026, h2029, h2031, hc45, hlam, hphi, ht0b, ht5b, p2032_1, u0elo3]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h0, h1871, h1951, h2025, h2026, h2029, h2031, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2032_1, u4elo1]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h2021, hlam, p2032_0]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [hlam, p2032_0]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  rcases p2032_3 (m.d 0 1) (by simp) with h2054 | h2054
                                  · linarith only [h1478, h2054, hlam]
                                  · linarith only [h1871, h2054, hlam]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h1871, hlam, p2032_0]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h2020, hlam, p2032_1]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h2022, hlam, p2032_0]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [h2023, hlam, p2032_1]
                                · have p2032_0 := h2032c.1
                                  have p2032_1 := h2032c.2.1
                                  have p2032_2 := h2032c.2.2.1
                                  have p2032_3 := h2032c.2.2.2
                                  linarith only [hlam, p2032_0]
                              · linarith only [h1951, h2023, h2025, h2031, hc34, hlam, hphi, u4elo1]
                            · linarith only [h1478, h1871, h1951, h2027, h2030, hc04, hlam, hphi, u4elo1]
                          · linarith only [h0, h1951, h2022, h2028, h2029, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1871, h1872, h2026, h2028, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h0, h1871, h1951, h2025, h2026, h2027, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h1872, h2020, h2026, hc12, hc23, hlam, hphi]
                  · linarith only [h1872, h2024, h2025, hc03, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2069 | h2069
                  · linarith only [h0, h1871, h1951, h2024, h2069, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h1871, h2069, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h0, h1871, h1951, h2023, hlam]
            · linarith only [h1079, h1871, h2022, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2074 | h2074
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2075 | h2075
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2076 | h2076
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2077 | h2077
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2078 | h2078
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2079 | h2079
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2080 | h2080
                        · linarith only [h0, h1871, h1872, h2021, h2076, h2078, h2080, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h1871, h1872, h2078, h2080, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h1478, h1871, h2078, h2079, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h0, h1871, h1951, h2020, h2077, h2078, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                  · linarith only [h2076, h2077, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2086 | h2086
                  · linarith only [h1951, h2076, h2086, hc02, hc23, hlam, hphi]
                  · linarith only [h0, h1871, h2086, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h1079, h1871, h2021, h2075, hlam]
            · linarith only [h0, h1871, h1872, h2074, hlam]
        · linarith only [h0, h1871, h2020, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2092 | h2092
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2093 | h2093
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2094 | h2094
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2095 | h2095
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2096 | h2096
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2097 | h2097
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2098 | h2098
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2099 | h2099
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2100 | h2100
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2101 | h2101
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2102 | h2102
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2103 | h2103
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2104 | h2104
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2105 | h2105
                              · linarith only [h2092, h2102, h2105, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h1478, h2097, h2105, hc34, hlam, hphi, u4elo1]
                            · linarith only [h1478, h2097, h2104, hc24, hlam, hphi, u4elo1]
                          · linarith only [h2092, h2096, h2102, h2103, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2110 | h2110
                          · linarith only [h2092, h2095, h2102, h2110, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2112 | h2112
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2113 | h2113
                              · rcases h0bigk with h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [hlam, p2114_0]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h0, hlam, p2114_1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h1079, hlam, p2114_0]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h1478, hlam, p2114_1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h1871, hlam, p2114_1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  rcases p2114_3 (m.d 0 1) (by simp) with h2120 | h2120
                                  · linarith only [h0, h2120, hlam]
                                  · rcases p2114_3 (m.d 0 2) (by simp) with h2122 | h2122
                                    · rcases p2114_3 (m.d 0 3) (by simp) with h2123 | h2123
                                      · linarith only [h2092, h2123, hlam]
                                      · linarith only [h1079, h2123, hlam]
                                    · linarith only [h0, h2122, hlam]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [hlam, p2114_0]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h2095, h2110, h2113, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2114_1, u0elo1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h2093, h2112, hc45, hlam, hphi, ht0b, ht5b, p2114_1, u0elo1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h2096, h2110, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2114_1, u0elo1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  rcases p2114_3 (m.d 0 1) (by simp) with h2131 | h2131
                                  · linarith only [h1079, h2131, hlam]
                                  · rcases p2114_3 (m.d 0 2) (by simp) with h2133 | h2133
                                    · rcases p2114_3 (m.d 0 3) (by simp) with h2134 | h2134
                                      · rcases p2114_3 (m.d 0 4) (by simp) with h2135 | h2135
                                        · linarith only [h2095, h2135, hlam]
                                        · linarith only [h1478, h2135, hlam]
                                      · linarith only [h1079, h2134, hlam]
                                    · linarith only [h0, h2133, hlam]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h2092, hlam, p2114_1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [hlam, p2114_0]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h2095, h2110, h2113, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2114_1, u0elo2]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h2092, h2096, h2110, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2114_1, u0elo1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2114_1, u4elo0]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h2093, hlam, p2114_0]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h2095, hlam, p2114_0]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [hlam, p2114_0]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h1478, h2096, h2110, hc23, hlam, hphi, ht34, p2114_1, u4elo1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h1871, h2101, hc01, hlam, hphi, ht12, ht23, ht34, p2114_1, u4elo1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h2094, hlam, p2114_1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h2096, hlam, p2114_0]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [h2097, hlam, p2114_1]
                                · have p2114_0 := h2114c.1
                                  have p2114_1 := h2114c.2.1
                                  have p2114_2 := h2114c.2.2.1
                                  have p2114_3 := h2114c.2.2.2
                                  linarith only [hlam, p2114_0]
                              · linarith only [h2112, h2113, hc34, hlam, hphi, u4elo2]
                            · linarith only [h1478, h2097, h2112, hc24, hlam, hphi, u4elo1]
                      · linarith only [h1478, h2097, h2101, hlam]
                    · linarith only [h0, h2094, h2100, hlam]
                  · linarith only [h0, h2092, h2095, h2099, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h2092, h2098, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2160 | h2160
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2161 | h2161
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2162 | h2162
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2163 | h2163
                      · linarith only [h1478, h2097, h2163, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1478, h2163, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h1079, h2094, h2160, h2162, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2093, h2161, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                · linarith only [h0, h2092, h2160, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2169 | h2169
              · linarith only [h2095, h2096, h2169, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2171 | h2171
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2172 | h2172
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2173 | h2173
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2174 | h2174
                      · linarith only [h2169, h2174, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1478, h2174, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2094, h2173, hlam]
                  · linarith only [h0, h2172, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2092, h2171, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2180 | h2180
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2181 | h2181
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2182 | h2182
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2183 | h2183
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2184 | h2184
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2185 | h2185
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2186 | h2186
                        · linarith only [h2092, h2095, h2186, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2188 | h2188
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2189 | h2189
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2190 | h2190
                              · rcases h0bigk with h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c | h2191c
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h0, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1079, hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1478, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1871, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  rcases p2191_3 (m.d 0 1) (by simp) with h2197 | h2197
                                  · linarith only [h0, h2197, hlam]
                                  · rcases p2191_3 (m.d 0 2) (by simp) with h2199 | h2199
                                    · rcases p2191_3 (m.d 0 3) (by simp) with h2200 | h2200
                                      · linarith only [h2092, h2200, hlam]
                                      · linarith only [h1079, h2200, hlam]
                                    · linarith only [h0, h2199, hlam]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2092, h2188, h2190, hc45, hlam, hphi, ht0b, ht5b, p2191_1, u0elo1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2092, h2095, h2188, h2190, hc45, hlam, hphi, ht0b, ht5b, p2191_1, u0elo1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  rcases p2191_3 (m.d 0 1) (by simp) with h2207 | h2207
                                  · linarith only [h0, h2207, hlam]
                                  · rcases p2191_3 (m.d 0 2) (by simp) with h2209 | h2209
                                    · rcases p2191_3 (m.d 0 3) (by simp) with h2210 | h2210
                                      · linarith only [h2092, h2210, hlam]
                                      · linarith only [h2180, h2210, hlam]
                                    · linarith only [h2094, h2209, hlam]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2095, hc01, hc34, hlam, hphi, ht12, ht23, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2092, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2095, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1871, h2095, hc01, hlam, hphi, ht12, ht23, ht34, p2191_1, u4elo3]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1478, hc01, hlam, hphi, ht12, ht23, ht34, p2191_1, u4elo1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2093, hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1478, hc03, hlam, hphi, ht34, p2191_1, u4elo1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h1478, h1871, hc01, hlam, hphi, ht12, ht23, ht34, p2191_1, u4elo1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2095, h2180, hc01, hlam, hphi, ht12, ht23, ht34, p2191_1, u4elo3]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2094, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2180, hlam, p2191_0]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [h2181, hlam, p2191_1]
                                · have p2191_0 := h2191c.1
                                  have p2191_1 := h2191c.2.1
                                  have p2191_2 := h2191c.2.2.1
                                  have p2191_3 := h2191c.2.2.2
                                  linarith only [hlam, p2191_0]
                              · linarith only [h2092, h2095, h2188, h2190, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h2095, h2180, h2181, h2186, h2188, h2189, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h2095, h2180, h2188, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h1478, h2095, h2180, h2181, h2185, hc04, hlam, hphi, u4elo3]
                    · linarith only [h0, h2094, h2184, hlam]
                  · linarith only [h0, h2183, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2092, h2182, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h2095, h2180, h2181, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2237 | h2237
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2238 | h2238
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2239 | h2239
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2240 | h2240
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2241 | h2241
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2242 | h2242
                        · linarith only [h2092, h2095, h2242, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2244 | h2244
                          · linarith only [h2180, h2242, h2244, hc03, hlam, hphi, ht34, u4elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2246 | h2246
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2247 | h2247
                              · rcases h0bigk with h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c | h2248c
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [hlam, p2248_0]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h0, hlam, p2248_1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h1079, hlam, p2248_0]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h1478, hlam, p2248_1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h1871, hlam, p2248_1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  rcases p2248_3 (m.d 0 1) (by simp) with h2254 | h2254
                                  · linarith only [h0, h2254, hlam]
                                  · rcases p2248_3 (m.d 0 2) (by simp) with h2256 | h2256
                                    · rcases p2248_3 (m.d 0 3) (by simp) with h2257 | h2257
                                      · linarith only [h2092, h2257, hlam]
                                      · linarith only [h1079, h2257, hlam]
                                    · linarith only [h0, h2256, hlam]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [hlam, p2248_0]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  rcases p2248_3 (m.d 0 1) (by simp) with h2262 | h2262
                                  · linarith only [h0, h2262, hlam]
                                  · rcases p2248_3 (m.d 0 2) (by simp) with h2264 | h2264
                                    · rcases p2248_3 (m.d 0 3) (by simp) with h2265 | h2265
                                      · linarith only [h2092, h2265, hlam]
                                      · rcases p2248_3 (m.d 0 4) (by simp) with h2267 | h2267
                                        · linarith only [h2093, h2267, hlam]
                                        · linarith only [h2095, h2267, hlam]
                                    · linarith only [h2092, h2264, hlam]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h2093, h2246, hc45, hlam, hphi, ht0b, ht5b, p2248_1, u0elo1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  rcases p2248_3 (m.d 0 1) (by simp) with h2272 | h2272
                                  · linarith only [h0, h2272, hlam]
                                  · rcases p2248_3 (m.d 0 2) (by simp) with h2274 | h2274
                                    · rcases p2248_3 (m.d 0 3) (by simp) with h2275 | h2275
                                      · linarith only [h2092, h2275, hlam]
                                      · rcases p2248_3 (m.d 0 4) (by simp) with h2277 | h2277
                                        · linarith only [h2093, h2277, hlam]
                                        · linarith only [h2237, h2277, hlam]
                                    · linarith only [h2094, h2274, hlam]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h2180, hc01, hc35, hlam, hphi, ht12, ht23, p2248_1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h2092, hlam, p2248_1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [hlam, p2248_0]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h2095, hlam, p2248_1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h2180, hlam, p2248_1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2248_1, u4elo0]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h2093, hlam, p2248_0]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h1478, hc03, hlam, hphi, ht34, p2248_1, u4elo1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [hlam, p2248_0]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h1478, h1871, hc01, hlam, hphi, ht12, ht23, ht34, p2248_1, u4elo1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h1478, h2237, hc01, hlam, hphi, ht12, ht23, ht34, p2248_1, u4elo1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h2094, hlam, p2248_1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h1079, h1478, h2237, hc01, hlam, hphi, ht12, ht23, ht34, p2248_1, u4elo1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [h2237, hlam, p2248_1]
                                · have p2248_0 := h2248c.1
                                  have p2248_1 := h2248c.2.1
                                  have p2248_2 := h2248c.2.2.1
                                  have p2248_3 := h2248c.2.2.2
                                  linarith only [hlam, p2248_0]
                              · linarith only [h2246, h2247, hc34, hlam, hphi, u4elo2]
                            · linarith only [h1478, h2237, h2246, hc24, hlam, hphi, u4elo1]
                      · linarith only [h1478, h2237, h2241, hlam]
                    · linarith only [h0, h2094, h2240, hlam]
                  · linarith only [h0, h2239, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2092, h2238, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2302 | h2302
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2303 | h2303
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2304 | h2304
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2305 | h2305
                      · linarith only [h2237, h2305, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1478, h2305, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h1079, h2094, h2302, h2304, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2093, h2303, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                · linarith only [h0, h2092, h2302, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2311 | h2311
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2312 | h2312
            · linarith only [h2092, h2094, h2312, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2314 | h2314
              · linarith only [h2093, h2094, h2314, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2316 | h2316
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2317 | h2317
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2318 | h2318
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2319 | h2319
                      · linarith only [h1478, h2314, h2319, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1478, h2319, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2322 | h2322
                      · linarith only [h1478, h2314, h2322, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1478, h2322, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h2093, h2317, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h2092, h2316, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2327 | h2327
            · linarith only [h2092, h2094, h2327, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2329 | h2329
              · linarith only [h2093, h2094, h2329, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2331 | h2331
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2332 | h2332
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2333 | h2333
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2334 | h2334
                      · linarith only [h2329, h2334, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1478, h2334, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2337 | h2337
                      · linarith only [h1079, h2311, h2329, h2337, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1478, h2337, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h2093, h2332, hlam]
                · linarith only [h0, h2092, h2331, hlam]
      · linarith only [h2092, h2093, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2343 | h2343
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2344 | h2344
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2345 | h2345
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2346 | h2346
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2347 | h2347
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2348 | h2348
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2349 | h2349
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2350 | h2350
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2351 | h2351
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2352 | h2352
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2353 | h2353
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2354 | h2354
                            · linarith only [h2092, h2343, h2348, h2354, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h2092, h2343, h2347, h2348, h2354, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h2092, h2346, h2353, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h2092, h2343, h2352, hc24, hlam, hphi, u4elo3]
                      · linarith only [h2347, h2351, hc14, hlam, hphi, u4elo0]
                    · linarith only [h2092, h2344, h2350, hc12, hc23, hlam, hphi]
                  · linarith only [h2092, h2348, h2349, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2362 | h2362
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2363 | h2363
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2364 | h2364
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2365 | h2365
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2366 | h2366
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2367 | h2367
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2368 | h2368
                              · rcases h0bigk with h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [hlam, p2369_0]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h0, hlam, p2369_1]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h1079, hlam, p2369_0]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h1478, hlam, p2369_1]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h1871, hlam, p2369_1]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h0, h2348, hc01, hc23, hlam, hphi, ht12, p2369_1]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [hlam, p2369_0]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h2092, hlam, p2369_0]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h0, h2343, h2348, h2365, h2368, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2369_1]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h0, h1871, h2348, hc01, hc23, hlam, hphi, ht12, p2369_1]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  rcases p2369_3 (m.d 0 1) (by simp) with h2380 | h2380
                                  · linarith only [h1079, h2380, hlam]
                                  · rcases p2369_3 (m.d 0 2) (by simp) with h2382 | h2382
                                    · linarith only [h2092, h2382, hlam]
                                    · linarith only [h0, h2382, hlam]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h2343, h2365, h2368, hc45, hlam, hphi, ht0b, ht5b, p2369_1, u0elo2]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [hlam, p2369_0]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h2343, h2365, h2368, hc45, hlam, hphi, ht0b, ht5b, p2369_1, u0elo2]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  rcases p2369_3 (m.d 0 1) (by simp) with h2388 | h2388
                                  · linarith only [h1079, h2388, hlam]
                                  · rcases p2369_3 (m.d 0 2) (by simp) with h2390 | h2390
                                    · linarith only [h2092, h2390, hlam]
                                    · linarith only [h2344, h2390, hlam]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2369_1, u4elo0]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h2343, hlam, p2369_0]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h2345, hlam, p2369_0]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [hlam, p2369_0]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h1478, h1871, hc01, hlam, hphi, ht12, ht23, ht34, p2369_1, u4elo1]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h1871, h2364, hc01, hlam, hphi, ht12, ht23, ht34, p2369_1, u4elo1]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h2344, hlam, p2369_1]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h2346, hlam, p2369_0]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [h2347, hlam, p2369_1]
                                · have p2369_0 := h2369c.1
                                  have p2369_1 := h2369c.2.1
                                  have p2369_2 := h2369c.2.2.1
                                  have p2369_3 := h2369c.2.2.2
                                  linarith only [hlam, p2369_0]
                              · linarith only [h1478, h2347, h2368, hc34, hlam, hphi, u4elo1]
                            · linarith only [h1478, h2347, h2365, h2367, hc34, hlam, hphi, u4elo1]
                          · linarith only [h0, h2348, h2366, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h2348, h2365, hc02, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h1478, h2343, h2347, h2364, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h2344, h2363, hlam]
                  · linarith only [h0, h2343, h2362, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2410 | h2410
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2411 | h2411
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2412 | h2412
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2413 | h2413
                      · linarith only [h2347, h2413, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1478, h2413, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h2092, h2344, h2410, h2412, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h2092, h2343, h2410, h2411, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2418 | h2418
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2419 | h2419
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2420 | h2420
                      · linarith only [h1478, h2347, h2420, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1478, h2420, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2344, h2419, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2418, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h2092, h2344, h2346, hlam]
          · linarith only [h2092, h2343, h2345, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2427 | h2427
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2428 | h2428
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2429 | h2429
              · linarith only [h2343, h2344, h2429, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2431 | h2431
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2432 | h2432
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2433 | h2433
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2434 | h2434
                      · linarith only [h1478, h2429, h2434, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1478, h2434, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h2092, h2431, h2433, hc02, hc25, hlam, hphi]
                  · linarith only [h2092, h2343, h2431, h2432, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2439 | h2439
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2440 | h2440
                    · linarith only [h2343, h2344, h2431, h2440, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2442 | h2442
                      · linarith only [h1478, h2429, h2442, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1478, h2442, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h2343, h2344, h2428, h2439, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2446 | h2446
              · linarith only [h2092, h2343, h2428, h2446, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2448 | h2448
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2449 | h2449
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2450 | h2450
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2451 | h2451
                      · linarith only [h2446, h2451, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1478, h2451, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h2092, h2343, h2448, h2450, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h2092, h2343, h2448, h2449, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2456 | h2456
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2457 | h2457
                    · linarith only [h2343, h2344, h2448, h2457, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2459 | h2459
                      · linarith only [h1478, h2446, h2459, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                      · linarith only [h1478, h2459, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h2092, h2343, h2428, h2456, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
          · linarith only [h2092, h2343, h2427, hc24, hlam, hphi, u4elo3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2464 | h2464
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2465 | h2465
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2466 | h2466
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2467 | h2467
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2468 | h2468
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2469 | h2469
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2470 | h2470
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2471 | h2471
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2472 | h2472
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2473 | h2473
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2474 | h2474
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2475 | h2475
                              · rcases h0bigk with h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [hlam, p2476_0]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h0, hlam, p2476_1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h1079, hlam, p2476_0]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h1478, hlam, p2476_1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h1871, hlam, p2476_1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h2343, h2469, hc01, hlam, hphi, ht12, ht23, ht34, p2476_1, u4elo1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [hlam, p2476_0]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h2092, hlam, p2476_0]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h2343, hlam, p2476_1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h2343, h2469, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2476_1, u4elo1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h2092, h2468, hc01, hc12, hlam, hphi, p2476_1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h2464, hc25, hlam, hphi, ht0b, ht5b, p2476_1, u0elo2]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [hlam, p2476_0]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h2343, h2464, h2473, h2475, hc45, hlam, hphi, ht0b, ht5b, p2476_1, u0elo2]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h1871, h2092, h2468, hc01, hc12, hlam, hphi, p2476_1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2476_1, u4elo0]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h1478, h2464, h2473, h2475, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2476_1, u4elo1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h2465, hlam, p2476_0]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [hlam, p2476_0]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h1478, h1871, hc01, hlam, hphi, ht12, ht23, ht34, p2476_1, u4elo1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h1871, h2471, hc01, hlam, hphi, ht12, ht23, ht34, p2476_1, u4elo1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h2464, hlam, p2476_1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h2466, hlam, p2476_0]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [h2467, hlam, p2476_1]
                                · have p2476_0 := h2476c.1
                                  have p2476_1 := h2476c.2.1
                                  have p2476_2 := h2476c.2.2.1
                                  have p2476_3 := h2476c.2.2.2
                                  linarith only [hlam, p2476_0]
                              · linarith only [h2343, h2467, h2469, h2475, hc34, hlam, hphi, u4elo1]
                            · linarith only [h2343, h2464, h2467, h2474, hlam]
                          · linarith only [h2092, h2466, h2473, hlam]
                        · linarith only [h2092, h2464, h2472, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h2343, h2464, h2465, h2467, h2469, h2471, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h2092, h2464, h2470, hc12, hc23, hlam, hphi]
                  · linarith only [h2092, h2468, h2469, hc03, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2509 | h2509
                  · linarith only [h2343, h2468, h2509, hc02, hc23, hlam, hphi]
                  · linarith only [h0, h2509, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h2343, h2464, h2467, hlam]
            · linarith only [h2343, h2464, h2465, h2466, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2514 | h2514
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2515 | h2515
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2516 | h2516
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2517 | h2517
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2518 | h2518
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2519 | h2519
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2520 | h2520
                        · linarith only [h2465, h2514, h2516, h2520, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1871, h2092, h2464, h2520, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h2515, h2517, h2519, hc24, hlam, hphi, u4elo0]
                    · linarith only [h2092, h2464, h2465, h2518, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1871, h2092, h2464, h2516, h2517, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2526 | h2526
                  · linarith only [h1871, h2343, h2464, h2516, h2526, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2526, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h2343, h2464, h2515, hlam]
            · linarith only [h2092, h2464, h2514, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2531 | h2531
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2532 | h2532
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2533 | h2533
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2534 | h2534
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2535 | h2535
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2536 | h2536
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2537 | h2537
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2538 | h2538
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2539 | h2539
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2540 | h2540
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2541 | h2541
                              · rcases h0bigk with h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c | h2542c
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [hlam, p2542_0]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h0, hlam, p2542_1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h1079, hlam, p2542_0]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h1478, hlam, p2542_1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h1871, hlam, p2542_1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h2464, h2534, h2538, h2540, hc01, hc12, hlam, hphi, p2542_1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [hlam, p2542_0]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h2092, hlam, p2542_0]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h2343, hlam, p2542_1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h2464, hlam, p2542_0]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h2092, h2534, hc01, hc12, hlam, hphi, p2542_1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h0, h2092, h2534, hc01, hc12, hlam, hphi, p2542_1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [hlam, p2542_0]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h1478, h2092, h2534, hc01, hc12, hlam, hphi, p2542_1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h0, h2092, h2464, h2534, hc01, hc12, hlam, hphi, p2542_1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2542_1, u4elo0]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h0, h1478, hc01, hlam, hphi, ht12, ht23, ht34, p2542_1, u4elo1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h2531, hlam, p2542_0]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [hlam, p2542_0]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h0, h1478, h2464, hc01, hlam, hphi, ht12, ht23, ht34, p2542_1, u4elo1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h2464, h2540, hc01, hlam, hphi, ht12, ht23, ht34, p2542_1, u4elo2]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h0, h2464, h2540, hc01, hlam, hphi, ht12, ht23, ht34, p2542_1, u4elo2]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h2532, hlam, p2542_0]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [h2533, hlam, p2542_1]
                                · have p2542_0 := h2542c.1
                                  have p2542_1 := h2542c.2.1
                                  have p2542_2 := h2542c.2.2.1
                                  have p2542_3 := h2542c.2.2.2
                                  linarith only [hlam, p2542_0]
                              · linarith only [h2343, h2533, h2535, h2541, hc34, hlam, hphi, u4elo1]
                            · linarith only [h2343, h2533, h2540, hlam]
                          · linarith only [h2092, h2532, h2539, hlam]
                        · linarith only [h0, h2092, h2538, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h2343, h2533, h2535, h2537, hlam]
                    · linarith only [h0, h2092, h2534, h2536, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2092, h2534, h2535, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2575 | h2575
                  · linarith only [h0, h2343, h2534, h2575, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2575, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2578 | h2578
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2579 | h2579
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2580 | h2580
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2581 | h2581
                      · linarith only [h2533, h2581, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1478, h2581, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2343, h2579, h2580, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2579, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2586 | h2586
                  · linarith only [h0, h2343, h2578, h2586, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2586, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2589 | h2589
              · linarith only [h2531, h2532, h2589, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2591 | h2591
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2592 | h2592
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2593 | h2593
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2594 | h2594
                      · linarith only [h2589, h2594, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1478, h2594, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2092, h2591, h2593, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2092, h2591, h2592, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2599 | h2599
                  · linarith only [h0, h2343, h2591, h2599, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2599, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2602 | h2602
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2603 | h2603
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2604 | h2604
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2605 | h2605
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2606 | h2606
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2607 | h2607
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2608 | h2608
                        · linarith only [h0, h2464, h2531, h2602, h2604, h2608, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2092, h2608, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h2603, h2605, h2607, hc24, hlam, hphi, u4elo0]
                    · linarith only [h0, h2092, h2604, h2606, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2092, h2604, h2605, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2614 | h2614
                  · linarith only [h0, h2343, h2604, h2614, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2614, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h2531, h2602, h2603, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2618 | h2618
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2619 | h2619
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2620 | h2620
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2621 | h2621
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2622 | h2622
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2623 | h2623
                        · linarith only [h1079, h2531, h2619, h2623, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2092, h2623, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h1478, h2622, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2092, h2619, h2621, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2092, h2619, h2620, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2629 | h2629
                  · linarith only [h0, h2343, h2619, h2629, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2629, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2632 | h2632
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2633 | h2633
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2634 | h2634
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2635 | h2635
                      · linarith only [h2618, h2635, hc04, hlam, hphi, u4elo1]
                      · linarith only [h1478, h2635, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h2092, h2632, h2634, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2092, h2632, h2633, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2640 | h2640
                  · linarith only [h0, h2343, h2632, h2640, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2640, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

set_option maxHeartbeats 5286000 in
set_option maxHeartbeats 5286000 in
theorem r1l7_20_12_14_M_LI_L_I_L_0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1079 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h1478 | h1478
  · exact r1l7_20_12_14_M_LI_L_I_L_0_x1_x1_x0 m hb0 hb2 hb4 h0 h1079 h1478
  · exact r1l7_20_12_14_M_LI_L_I_L_0_x1_x1_x1 m hb0 hb2 hb4 h0 h1079 h1478

set_option maxHeartbeats 5286000 in
set_option maxHeartbeats 5286000 in
theorem r1l7_20_12_14_M_LI_L_I_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h1079 | h1079
  · exact r1l7_20_12_14_M_LI_L_I_L_0_x1_x0 m hb0 hb2 hb4 h0 h1079
  · exact r1l7_20_12_14_M_LI_L_I_L_0_x1_x1 m hb0 hb2 hb4 h0 h1079

set_option maxHeartbeats 5286000 in
set_option maxHeartbeats 5286000 in
theorem r1l7_20_12_14_M_LI_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_M_LI_L_I_L_0_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_M_LI_L_I_L_0_x1 m hb0 hb2 hb4 h0

end R2N4
