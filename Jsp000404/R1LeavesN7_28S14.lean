import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_28S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6976000 in
set_option maxHeartbeats 6976000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1833 | h1833
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1834 | h1834
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1835 | h1835
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1836 | h1836
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1837 | h1837
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1838 | h1838
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1839 | h1839
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1840 | h1840
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1841 | h1841
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1842 | h1842
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1843 | h1843
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1844 | h1844
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1845 | h1845
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1846 | h1846
                            · linarith only [h1833, h1846, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h0, h1833, h1840, h1845, h1846, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1849 | h1849
                            · linarith only [h0, h1833, h1849, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1851 | h1851
                              · linarith only [h0, h1833, h1839, h1845, h1851, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1853 | h1853
                                · linarith only [h0, h1833, h1839, h1841, h1842, h1845, h1851, h1853, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1855 | h1855
                                  · linarith only [h0, h1833, h1839, h1841, h1842, h1845, h1851, h1855, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1857 | h1857
                                    · linarith only [h1843, h1851, h1857, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1859 | h1859
                                      · linarith only [h0, h1833, h1839, h1845, h1851, h1859, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                      · linarith only [h0, h1833, h1839, h1841, h1842, h1845, h1859, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1833, h1840, h1844, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h1835, h1843, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h1833, h1839, h1841, h1842, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1865 | h1865
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1866 | h1866
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1867 | h1867
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1868 | h1868
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1869 | h1869
                            · linarith only [h1833, h1869, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h1840, h1868, h1869, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1872 | h1872
                            · linarith only [h1839, h1868, h1872, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1874 | h1874
                              · linarith only [h0, h1833, h1839, h1841, h1868, h1874, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1876 | h1876
                                · linarith only [h1865, h1868, h1876, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1878 | h1878
                                  · linarith only [h1865, h1872, h1878, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1880 | h1880
                                    · linarith only [h1837, h1839, h1841, h1865, h1868, h1880, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1882 | h1882
                                      · linarith only [h1839, h1841, h1882, hlam]
                                      · rcases h0bigk with h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [hlam, p1884_0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h0, hlam, p1884_1]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h0, h1840, h1865, h1868, h1882, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1884_1]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h0, h1839, h1865, h1868, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1884_1]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1884_1, u5ehi0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1833, h1865, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1884_1, u0elo1]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [hlam, p1884_0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1840, h1865, h1868, h1882, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1884_1, u0elo1]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1839, h1865, h1868, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1884_1, u0elo1]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1835, h1867, hlam, hphi, ht0b, ht5b, p1884_1, u0elo1, u5ehi2]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1833, hlam, p1884_1]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1836, hlam, p1884_1]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [hlam, p1884_0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1833, h1839, h1865, h1868, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1884_1, u0elo0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h0, h1833, h1835, h1867, hc12, hlam, hphi, ht01, ht0b, ht5b, p1884_1, u5ehi2]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1834, hlam, p1884_0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1837, hlam, p1884_0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1839, hlam, p1884_0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [hlam, p1884_0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1841, hlam, p1884_0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1835, hlam, p1884_0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1838, hlam, p1884_1]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1840, hlam, p1884_0]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [h1839, h1865, h1868, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1884_1, u0elo4]
                                        · have p1884_0 := h1884c.1
                                          have p1884_1 := h1884c.2.1
                                          have p1884_2 := h1884c.2.2.1
                                          have p1884_3 := h1884c.2.2.2
                                          linarith only [hlam, p1884_0]
                        · linarith only [h0, h1835, h1867, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h1833, h1840, h1866, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h1833, h1840, h1865, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1913 | h1913
                  · linarith only [h1839, h1840, h1913, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1915 | h1915
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1916 | h1916
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1917 | h1917
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1918 | h1918
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1919 | h1919
                            · linarith only [h1833, h1840, h1919, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1921 | h1921
                              · linarith only [h0, h1834, h1913, h1921, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1923 | h1923
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1924 | h1924
                                  · linarith only [h1836, h1840, h1924, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1926 | h1926
                                    · linarith only [h0, h1834, h1913, h1916, h1926, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1928 | h1928
                                      · linarith only [h1833, h1913, h1915, h1923, h1928, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                      · rcases h0bigk with h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c | h1930c
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [hlam, p1930_0]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h0, hlam, p1930_1]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h0, h1839, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1930_1]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          rcases p1930_3 (m.d 0 1) (by simp) with h1934 | h1934
                                          · rcases p1930_3 (m.d 0 2) (by simp) with h1935 | h1935
                                            · rcases p1930_3 (m.d 0 3) (by simp) with h1936 | h1936
                                              · linarith only [h1833, h1936, hlam]
                                              · linarith only [h1839, h1936, hlam]
                                            · linarith only [h1837, h1935, hlam]
                                          · linarith only [h1834, h1934, hlam]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1930_1, u5ehi0]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1833, h1915, h1923, hc34, hlam, hphi, ht0b, ht45, ht5b, p1930_1, u0elo1]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [hlam, p1930_0]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1833, h1915, h1923, hc34, hlam, hphi, ht0b, ht45, ht5b, p1930_1, u0elo1]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          rcases p1930_3 (m.d 0 1) (by simp) with h1945 | h1945
                                          · linarith only [h0, h1945, hlam]
                                          · linarith only [h1834, h1945, hlam]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1833, h1840, h1915, h1923, hc34, hlam, hphi, ht0b, ht45, ht5b, p1930_1, u0elo1]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1833, hlam, p1930_1]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1836, hlam, p1930_1]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [hlam, p1930_0]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1834, h1840, h1916, h1923, h1928, hc34, hc45, hlam, hphi, p1930_1]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1840, hlam, p1930_1]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1834, hlam, p1930_0]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1837, hlam, p1930_0]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1839, hlam, p1930_0]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [hlam, p1930_0]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1913, hlam, p1930_0]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1835, hlam, p1930_0]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1838, hlam, p1930_1]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [h1833, h1915, h1923, hc34, hlam, hphi, ht0b, ht45, ht5b, p1930_1, u0elo4]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          rcases p1930_3 (m.d 0 1) (by simp) with h1962 | h1962
                                          · rcases p1930_3 (m.d 0 2) (by simp) with h1963 | h1963
                                            · rcases p1930_3 (m.d 0 3) (by simp) with h1964 | h1964
                                              · linarith only [h1840, h1964, hlam]
                                              · linarith only [h1839, h1964, hlam]
                                            · linarith only [h1837, h1963, hlam]
                                          · linarith only [h1834, h1962, hlam]
                                        · have p1930_0 := h1930c.1
                                          have p1930_1 := h1930c.2.1
                                          have p1930_2 := h1930c.2.2.1
                                          have p1930_3 := h1930c.2.2.2
                                          linarith only [hlam, p1930_0]
                                · linarith only [h1839, h1840, h1923, hc23, hc35, hlam, hphi]
                          · linarith only [h1839, h1840, h1918, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h1835, h1917, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h1835, h1916, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h1835, h1915, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1975 | h1975
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1976 | h1976
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1977 | h1977
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1978 | h1978
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1979 | h1979
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1980 | h1980
                          · linarith only [h1839, h1975, h1980, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1982 | h1982
                            · linarith only [h1834, h1980, h1982, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                            · linarith only [h1839, h1975, h1977, h1982, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h1835, h1979, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h1834, h1839, h1975, h1978, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h1834, h1839, h1975, h1977, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h1839, h1975, h1976, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1989 | h1989
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1990 | h1990
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1991 | h1991
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1992 | h1992
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1993 | h1993
                          · linarith only [h1833, h1839, h1989, h1993, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1995 | h1995
                            · linarith only [h1834, h1975, h1993, h1995, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1997 | h1997
                              · linarith only [h0, h1834, h1997, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1999 | h1999
                                · linarith only [h1833, h1839, h1989, h1990, h1997, h1999, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2001 | h2001
                                  · linarith only [h0, h1834, h1975, h1989, h1990, h1993, h1997, h2001, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2003 | h2003
                                    · linarith only [h1837, h1993, h1997, h2003, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2005 | h2005
                                      · rcases h0bigk with h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c | h2006c
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [hlam, p2006_0]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h0, hlam, p2006_1]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          rcases p2006_3 (m.d 0 1) (by simp) with h2009 | h2009
                                          · rcases p2006_3 (m.d 0 2) (by simp) with h2010 | h2010
                                            · rcases p2006_3 (m.d 0 3) (by simp) with h2011 | h2011
                                              · linarith only [h1833, h2011, hlam]
                                              · rcases p2006_3 (m.d 0 4) (by simp) with h2013 | h2013
                                                · linarith only [h1834, h2013, hlam]
                                                · linarith only [h1839, h2013, hlam]
                                            · linarith only [h1836, h2010, hlam]
                                          · linarith only [h1833, h2009, hlam]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h0, h1989, h1990, h1993, h1997, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2006_1]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2006_1, u5ehi0]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1833, h1990, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2006_1, u0elo1]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [hlam, p2006_0]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          rcases p2006_3 (m.d 0 1) (by simp) with h2022 | h2022
                                          · linarith only [h0, h2022, hlam]
                                          · linarith only [h1833, h2022, hlam]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1989, h1990, h1993, h1997, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2006_1, u0elo1]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1989, h1990, h1993, h1997, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2006_1, u0elo1]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1833, hlam, p2006_1]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1836, hlam, p2006_1]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [hlam, p2006_0]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1839, hlam, p2006_1]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1975, hlam, p2006_1]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1834, hlam, p2006_0]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1837, hlam, p2006_0]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          rcases p2006_3 (m.d 0 1) (by simp) with h2034 | h2034
                                          · rcases p2006_3 (m.d 0 2) (by simp) with h2035 | h2035
                                            · rcases p2006_3 (m.d 0 3) (by simp) with h2036 | h2036
                                              · linarith only [h1839, h2036, hlam]
                                              · rcases p2006_3 (m.d 0 4) (by simp) with h2038 | h2038
                                                · rcases p2006_3 (m.d 0 5) (by simp) with h2039 | h2039
                                                  · linarith only [h1989, h2039, hlam]
                                                  · linarith only [h1975, h2039, hlam]
                                                · linarith only [h1839, h2038, hlam]
                                            · linarith only [h1836, h2035, hlam]
                                          · linarith only [h1833, h2034, hlam]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [hlam, p2006_0]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1834, h1989, h1990, h1993, h1997, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2006_1, u0elo0]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1835, hlam, p2006_0]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1838, hlam, p2006_1]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          rcases p2006_3 (m.d 0 1) (by simp) with h2049 | h2049
                                          · rcases p2006_3 (m.d 0 2) (by simp) with h2050 | h2050
                                            · rcases p2006_3 (m.d 0 3) (by simp) with h2051 | h2051
                                              · linarith only [h1975, h2051, hlam]
                                              · rcases p2006_3 (m.d 0 4) (by simp) with h2053 | h2053
                                                · rcases p2006_3 (m.d 0 5) (by simp) with h2054 | h2054
                                                  · rcases h2bigk with h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h0, hlam, p2055_1]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      rcases p2055_3 (m.d 0 2) (by simp) with h2058 | h2058
                                                      · rcases p2055_3 (m.d 1 2) (by simp) with h2059 | h2059
                                                        · rcases p2055_3 (m.d 2 3) (by simp) with h2060 | h2060
                                                          · linarith only [h2060, hlam, p2055_0]
                                                          · rcases p2055_3 (m.d 2 4) (by simp) with h2062 | h2062
                                                            · linarith only [h1837, h2062, hlam]
                                                            · linarith only [h1999, h2062, hlam]
                                                        · linarith only [h1990, h2059, hlam]
                                                      · linarith only [h2058, hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      rcases p2055_3 (m.d 0 2) (by simp) with h2067 | h2067
                                                      · rcases p2055_3 (m.d 1 2) (by simp) with h2068 | h2068
                                                        · rcases p2055_3 (m.d 2 3) (by simp) with h2069 | h2069
                                                          · linarith only [h1836, h2069, hlam]
                                                          · rcases p2055_3 (m.d 2 4) (by simp) with h2071 | h2071
                                                            · linarith only [h2071, hlam, p2055_0]
                                                            · rcases p2055_3 (m.d 2 5) (by simp) with h2073 | h2073
                                                              · linarith only [h1838, h2073, hlam]
                                                              · linarith only [h2003, h2073, hlam]
                                                        · linarith only [h1991, h2068, hlam]
                                                      · linarith only [h2067, hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [hlam, hphi, ht0b, ht5b, p2055_1, u0elo1, u5ehi2]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h0, h1835, hc12, hlam, hphi, ht01, ht0b, ht5b, p2055_1, u5ehi1]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h0, h1833, h1834, h1989, h1990, hlam, p2006_1, p2055_2]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h0, h1834, h1989, h1991, h1997, hlam, p2055_2]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      rcases p2055_3 (m.d 0 2) (by simp) with h2083 | h2083
                                                      · linarith only [h0, h2083, hlam]
                                                      · linarith only [h1838, h2083, hlam]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h1836, hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h1990, hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h1999, hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h2001, hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h1837, hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h1991, hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h1834, h1989, h1991, h1997, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2055_1, u0elo0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h2003, hlam, p2055_1]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h1838, hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h1992, hlam, p2055_0]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h0, h1835, h1992, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2055_1, u0elo1]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [h0, h1834, h1989, h1992, h1997, hc24, hlam, hphi, ht0b, ht45, ht5b, p2055_1, u0elo1]
                                                    · have p2055_0 := h2055c.1
                                                      have p2055_1 := h2055c.2.1
                                                      have p2055_2 := h2055c.2.2.1
                                                      have p2055_3 := h2055c.2.2.2
                                                      linarith only [hlam, p2055_0]
                                                  · linarith only [h1975, h2054, hlam]
                                                · linarith only [h1839, h2053, hlam]
                                            · linarith only [h1836, h2050, hlam]
                                          · linarith only [h1833, h2049, hlam]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [h1989, hlam, p2006_1]
                                        · have p2006_0 := h2006c.1
                                          have p2006_1 := h2006c.2.1
                                          have p2006_2 := h2006c.2.2.1
                                          have p2006_3 := h2006c.2.2.2
                                          linarith only [hlam, p2006_0]
                                      · linarith only [h0, h1833, h1834, h1839, h1989, h1990, h2005, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1834, h1989, h1992, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h1834, h1989, h1991, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h1834, h1989, h1990, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2111 | h2111
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2112 | h2112
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2113 | h2113
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2114 | h2114
                          · linarith only [h1833, h1839, h2114, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2116 | h2116
                            · linarith only [h0, h1833, h1975, h2116, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2118 | h2118
                              · linarith only [h1834, h1989, h2118, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2120 | h2120
                                · linarith only [h1836, h1839, h2120, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2122 | h2122
                                  · linarith only [h1833, h1975, h2111, h2122, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2124 | h2124
                                    · linarith only [h1834, h1989, h2112, h2124, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2126 | h2126
                                      · rcases h0bigk with h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c | h2127c
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [hlam, p2127_0]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h0, hlam, p2127_1]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          rcases p2127_3 (m.d 0 1) (by simp) with h2130 | h2130
                                          · rcases p2127_3 (m.d 0 2) (by simp) with h2131 | h2131
                                            · rcases p2127_3 (m.d 0 3) (by simp) with h2132 | h2132
                                              · linarith only [h1833, h2132, hlam]
                                              · rcases p2127_3 (m.d 0 4) (by simp) with h2134 | h2134
                                                · linarith only [h1834, h2134, hlam]
                                                · linarith only [h1839, h2134, hlam]
                                            · linarith only [h1836, h2131, hlam]
                                          · linarith only [h1833, h2130, hlam]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          rcases p2127_3 (m.d 0 1) (by simp) with h2139 | h2139
                                          · rcases p2127_3 (m.d 0 2) (by simp) with h2140 | h2140
                                            · rcases p2127_3 (m.d 0 3) (by simp) with h2141 | h2141
                                              · linarith only [h1833, h2141, hlam]
                                              · rcases p2127_3 (m.d 0 4) (by simp) with h2143 | h2143
                                                · linarith only [h1834, h2143, hlam]
                                                · rcases p2127_3 (m.d 0 5) (by simp) with h2145 | h2145
                                                  · linarith only [h1835, h2145, hlam]
                                                  · linarith only [h1989, h2145, hlam]
                                            · linarith only [h1837, h2140, hlam]
                                          · linarith only [h1834, h2139, hlam]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h0, h1835, h2113, hc12, hlam, hphi, ht01, ht0b, ht5b, p2127_1, u5ehi2]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1833, h2111, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2127_1, u0elo1]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [hlam, p2127_0]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          rcases p2127_3 (m.d 0 1) (by simp) with h2153 | h2153
                                          · linarith only [h0, h2153, hlam]
                                          · linarith only [h1833, h2153, hlam]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          rcases p2127_3 (m.d 0 1) (by simp) with h2156 | h2156
                                          · linarith only [h0, h2156, hlam]
                                          · linarith only [h1834, h2156, hlam]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1835, h2113, hlam, hphi, ht0b, ht5b, p2127_1, u0elo1, u5ehi2]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1833, hlam, p2127_1]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1836, hlam, p2127_1]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [hlam, p2127_0]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1839, hlam, p2127_1]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1975, hlam, p2127_1]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1834, hlam, p2127_0]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1837, hlam, p2127_0]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1833, h1989, h2111, h2126, hc23, hc34, hlam, hphi, p2127_1]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [hlam, p2127_0]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1989, hlam, p2127_0]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1835, hlam, p2127_0]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1838, hlam, p2127_1]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1833, h1989, h2111, h2126, hc23, hc34, hlam, hphi, p2127_1]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [h1837, h1989, h2120, h2126, hc23, hc34, hlam, hphi, p2127_1]
                                        · have p2127_0 := h2127c.1
                                          have p2127_1 := h2127c.2.1
                                          have p2127_2 := h2127c.2.2.1
                                          have p2127_3 := h2127c.2.2.2
                                          linarith only [hlam, p2127_0]
                                      · rcases h0bigk with h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c | h2175c
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [hlam, p2175_0]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h0, hlam, p2175_1]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          rcases p2175_3 (m.d 0 1) (by simp) with h2178 | h2178
                                          · rcases p2175_3 (m.d 0 2) (by simp) with h2179 | h2179
                                            · rcases p2175_3 (m.d 0 3) (by simp) with h2180 | h2180
                                              · linarith only [h1833, h2180, hlam]
                                              · rcases p2175_3 (m.d 0 4) (by simp) with h2182 | h2182
                                                · linarith only [h1834, h2182, hlam]
                                                · linarith only [h1839, h2182, hlam]
                                            · linarith only [h1836, h2179, hlam]
                                          · linarith only [h1833, h2178, hlam]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          rcases p2175_3 (m.d 0 1) (by simp) with h2187 | h2187
                                          · rcases p2175_3 (m.d 0 2) (by simp) with h2188 | h2188
                                            · rcases p2175_3 (m.d 0 3) (by simp) with h2189 | h2189
                                              · linarith only [h1833, h2189, hlam]
                                              · rcases p2175_3 (m.d 0 4) (by simp) with h2191 | h2191
                                                · linarith only [h1834, h2191, hlam]
                                                · rcases p2175_3 (m.d 0 5) (by simp) with h2193 | h2193
                                                  · linarith only [h1835, h2193, hlam]
                                                  · linarith only [h1989, h2193, hlam]
                                            · linarith only [h1837, h2188, hlam]
                                          · linarith only [h1834, h2187, hlam]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2175_1, u5ehi0]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1833, h2111, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2175_1, u0elo1]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [hlam, p2175_0]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          rcases p2175_3 (m.d 0 1) (by simp) with h2201 | h2201
                                          · linarith only [h0, h2201, hlam]
                                          · linarith only [h1833, h2201, hlam]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          rcases p2175_3 (m.d 0 1) (by simp) with h2204 | h2204
                                          · linarith only [h0, h2204, hlam]
                                          · linarith only [h1834, h2204, hlam]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1835, h2113, hlam, hphi, ht0b, ht5b, p2175_1, u0elo1, u5ehi2]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1833, hlam, p2175_1]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1836, hlam, p2175_1]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [hlam, p2175_0]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1839, hlam, p2175_1]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1975, hlam, p2175_1]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1834, hlam, p2175_0]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1837, hlam, p2175_0]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1833, h1989, h2111, hc23, hc45, hlam, hphi, ht34, p2175_1]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [hlam, p2175_0]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1989, hlam, p2175_0]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1835, hlam, p2175_0]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [h1838, hlam, p2175_1]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          rcases p2175_3 (m.d 0 1) (by simp) with h2220 | h2220
                                          · rcases p2175_3 (m.d 0 2) (by simp) with h2221 | h2221
                                            · rcases p2175_3 (m.d 0 3) (by simp) with h2222 | h2222
                                              · linarith only [h1975, h2222, hlam]
                                              · rcases p2175_3 (m.d 0 4) (by simp) with h2224 | h2224
                                                · linarith only [h1989, h2224, hlam]
                                                · linarith only [h1839, h2224, hlam]
                                            · linarith only [h1836, h2221, hlam]
                                          · linarith only [h1833, h2220, hlam]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          rcases p2175_3 (m.d 0 1) (by simp) with h2229 | h2229
                                          · rcases p2175_3 (m.d 0 2) (by simp) with h2230 | h2230
                                            · rcases p2175_3 (m.d 0 3) (by simp) with h2231 | h2231
                                              · linarith only [h1975, h2231, hlam]
                                              · rcases p2175_3 (m.d 0 4) (by simp) with h2233 | h2233
                                                · linarith only [h1989, h2233, hlam]
                                                · rcases p2175_3 (m.d 0 5) (by simp) with h2235 | h2235
                                                  · rcases h2bigk with h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h0, hlam, p2236_1]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      rcases p2236_3 (m.d 0 2) (by simp) with h2239 | h2239
                                                      · rcases p2236_3 (m.d 1 2) (by simp) with h2240 | h2240
                                                        · rcases p2236_3 (m.d 2 3) (by simp) with h2241 | h2241
                                                          · linarith only [h2241, hlam, p2236_0]
                                                          · rcases p2236_3 (m.d 2 4) (by simp) with h2243 | h2243
                                                            · linarith only [h1837, h2243, hlam]
                                                            · linarith only [h2120, h2243, hlam]
                                                        · linarith only [h2111, h2240, hlam]
                                                      · linarith only [h2239, hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      rcases p2236_3 (m.d 0 2) (by simp) with h2248 | h2248
                                                      · rcases p2236_3 (m.d 1 2) (by simp) with h2249 | h2249
                                                        · rcases p2236_3 (m.d 2 3) (by simp) with h2250 | h2250
                                                          · linarith only [h1836, h2250, hlam]
                                                          · rcases p2236_3 (m.d 2 4) (by simp) with h2252 | h2252
                                                            · linarith only [h2252, hlam, p2236_0]
                                                            · rcases p2236_3 (m.d 2 5) (by simp) with h2254 | h2254
                                                              · linarith only [h1838, h2254, hlam]
                                                              · linarith only [h2124, h2254, hlam]
                                                        · linarith only [h2112, h2249, hlam]
                                                      · linarith only [h2248, hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [hlam, hphi, ht0b, ht5b, p2236_1, u0elo1, u5ehi2]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h0, h1833, h1835, h1839, h2111, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2175_1, p2236_1]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h0, h1833, h1835, h1839, h2111, hlam, p2175_1, p2236_2]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h0, h1835, h1837, hlam, p2175_1, p2236_2]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      rcases p2236_3 (m.d 0 2) (by simp) with h2264 | h2264
                                                      · linarith only [h0, h2264, hlam]
                                                      · linarith only [h1838, h2264, hlam]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h1836, hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h2111, hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h2120, hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h2122, hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h1837, hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h2112, hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h1834, h1835, h2112, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2175_1, p2236_1, u0elo0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h2124, hlam, p2236_1]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h1838, hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h2113, hlam, p2236_0]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h1838, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2236_1, u0elo1]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [h0, h1835, h2113, hc24, hlam, hphi, ht0b, ht45, ht5b, p2236_1, u0elo1]
                                                    · have p2236_0 := h2236c.1
                                                      have p2236_1 := h2236c.2.1
                                                      have p2236_2 := h2236c.2.2.1
                                                      have p2236_3 := h2236c.2.2.2
                                                      linarith only [hlam, p2236_0]
                                                  · linarith only [h1989, h2235, hlam]
                                            · linarith only [h1837, h2230, hlam]
                                          · linarith only [h1834, h2229, hlam]
                                        · have p2175_0 := h2175c.1
                                          have p2175_1 := h2175c.2.1
                                          have p2175_2 := h2175c.2.2.1
                                          have p2175_3 := h2175c.2.2.2
                                          linarith only [hlam, p2175_0]
                        · linarith only [h0, h1835, h2113, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h1835, h2112, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h1835, h2111, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h1835, h1838, hlam]
          · linarith only [h0, h1834, h1837, hlam]
        · linarith only [h0, h1833, h1836, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2292 | h2292
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2293 | h2293
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2294 | h2294
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2295 | h2295
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2296 | h2296
                · linarith only [h1833, h1835, h2296, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2298 | h2298
                  · linarith only [h1833, h1835, h2295, h2298, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2300 | h2300
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2301 | h2301
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2302 | h2302
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2303 | h2303
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2304 | h2304
                            · linarith only [h1833, h1835, h2294, h2296, h2304, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2306 | h2306
                              · linarith only [h1834, h1835, h2304, h2306, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · linarith only [h1833, h1835, h2303, h2306, hc34, hc45, hlam, hphi]
                          · linarith only [h2295, h2296, h2303, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h1833, h2294, h2295, h2302, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h2293, h2301, hlam]
                    · linarith only [h0, h2292, h2300, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2313 | h2313
                · linarith only [h1834, h1835, h2295, h2313, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2315 | h2315
                  · linarith only [h1834, h1835, h2315, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2317 | h2317
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2318 | h2318
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2319 | h2319
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2320 | h2320
                          · linarith only [h1833, h1835, h2294, h2295, h2320, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2322 | h2322
                            · linarith only [h1833, h1835, h2313, h2322, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2324 | h2324
                              · linarith only [h1834, h2295, h2315, h2324, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2326 | h2326
                                · linarith only [h1833, h1835, h2317, h2324, h2326, hc34, hc45, hlam, hphi]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2328 | h2328
                                  · linarith only [h1833, h1835, h2317, h2324, h2328, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2330 | h2330
                                    · linarith only [h1834, h1835, h2318, h2324, h2330, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2332 | h2332
                                      · linarith only [h1834, h1835, h2320, h2324, h2332, hc13, hc34, hlam, hphi]
                                      · rcases h0bigk with h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c | h2334c
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [hlam, p2334_0]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h0, hlam, p2334_1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h1835, h2322, hc03, hc35, hlam, hphi, p2334_1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h1833, h1835, h2295, h2317, h2322, hc23, hc35, hlam, hphi, p2334_1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h1835, hlam, p2334_1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h1833, h2317, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2334_1, u0elo1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [hlam, p2334_0]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          rcases p2334_3 (m.d 0 1) (by simp) with h2342 | h2342
                                          · linarith only [h0, h2342, hlam]
                                          · linarith only [h1833, h2342, hlam]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          rcases p2334_3 (m.d 0 1) (by simp) with h2345 | h2345
                                          · linarith only [h0, h2345, hlam]
                                          · linarith only [h1834, h2345, hlam]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h1834, h1835, h2317, h2320, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2334_1, u0elo1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h1833, hlam, p2334_1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h2292, hlam, p2334_1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [hlam, p2334_0]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h2295, hlam, p2334_1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h2313, hlam, p2334_1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h1834, hlam, p2334_0]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h2293, hlam, p2334_0]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h1833, h1834, h1835, h2317, h2322, h2332, hc23, hc45, hlam, hphi, ht34, p2334_1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [hlam, p2334_0]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h2315, hlam, p2334_0]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h1833, h2317, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2334_1, u0elo4]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [h2294, hlam, p2334_1]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          rcases p2334_3 (m.d 0 1) (by simp) with h2361 | h2361
                                          · linarith only [h1835, h2361, hlam]
                                          · linarith only [h1833, h2361, hlam]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          rcases p2334_3 (m.d 0 1) (by simp) with h2364 | h2364
                                          · linarith only [h1835, h2364, hlam]
                                          · linarith only [h1834, h2364, hlam]
                                        · have p2334_0 := h2334c.1
                                          have p2334_1 := h2334c.2.1
                                          have p2334_2 := h2334c.2.2.1
                                          have p2334_3 := h2334c.2.2.2
                                          linarith only [hlam, p2334_0]
                        · linarith only [h0, h2294, h2319, hlam]
                      · linarith only [h0, h2293, h2318, hlam]
                    · linarith only [h0, h2292, h2317, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2371 | h2371
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2372 | h2372
                · linarith only [h0, h1833, h2294, h2372, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2374 | h2374
                  · linarith only [h0, h1833, h2294, h2371, h2374, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2376 | h2376
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2377 | h2377
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2378 | h2378
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2379 | h2379
                          · linarith only [h0, h1833, h2294, h2378, h2379, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h1833, h2294, h2371, h2378, h2379, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2382 | h2382
                          · linarith only [h0, h1833, h2378, h2382, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h2371, h2372, h2382, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h2293, h2377, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h2292, h2376, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2387 | h2387
                · linarith only [h1834, h1835, h2371, h2387, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2389 | h2389
                  · linarith only [h0, h1834, h2294, h2389, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2391 | h2391
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2392 | h2392
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2393 | h2393
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2394 | h2394
                          · linarith only [h0, h1833, h2294, h2371, h2393, h2394, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2396 | h2396
                            · linarith only [h0, h1833, h2294, h2387, h2396, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2398 | h2398
                              · linarith only [h0, h1834, h2294, h2389, h2393, h2398, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2400 | h2400
                                · linarith only [h1833, h2371, h2391, h2400, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2402 | h2402
                                  · linarith only [h0, h1833, h2294, h2371, h2391, h2393, h2396, h2402, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2404 | h2404
                                    · linarith only [h2293, h2294, h2393, h2398, h2404, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2406 | h2406
                                      · linarith only [h0, h1834, h2294, h2391, h2393, h2394, h2398, h2406, hc23, hc34, hlam, hphi]
                                      · rcases h0bigk with h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [hlam, p2408_0]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h0, hlam, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h0, h2294, h2393, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h0, h2294, h2393, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h1835, hlam, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h2294, h2393, hc01, hc12, hlam, hphi, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [hlam, p2408_0]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h1833, h2294, h2391, h2393, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h1834, h2294, h2391, h2393, h2394, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h2294, hlam, p2408_0]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h1833, hlam, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h2292, hlam, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [hlam, p2408_0]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h2371, hlam, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h2387, hlam, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h1834, hlam, p2408_0]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h2293, hlam, p2408_0]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h0, h1833, h1834, h2294, h2391, h2393, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [hlam, p2408_0]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h2389, hlam, p2408_0]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h1833, h2391, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2408_1, u0elo4]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [h0, h1834, h2294, h2391, h2393, h2394, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2408_1]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          rcases p2408_3 (m.d 0 1) (by simp) with h2431 | h2431
                                          · linarith only [h1835, h2431, hlam]
                                          · linarith only [h1833, h2431, hlam]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          rcases p2408_3 (m.d 0 1) (by simp) with h2434 | h2434
                                          · linarith only [h1835, h2434, hlam]
                                          · linarith only [h1834, h2434, hlam]
                                        · have p2408_0 := h2408c.1
                                          have p2408_1 := h2408c.2.1
                                          have p2408_2 := h2408c.2.2.1
                                          have p2408_3 := h2408c.2.2.2
                                          linarith only [hlam, p2408_0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2438 | h2438
                          · linarith only [h0, h1833, h2393, h2438, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2440 | h2440
                            · linarith only [h0, h1834, h2393, h2438, h2440, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2442 | h2442
                              · linarith only [h0, h1834, h2393, h2442, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2444 | h2444
                                · linarith only [h0, h1834, h2371, h2391, h2393, h2438, h2444, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2446 | h2446
                                  · linarith only [h0, h1833, h1835, h2391, h2393, h2440, h2446, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                                  · linarith only [h0, h1834, h2392, h2393, h2444, h2446, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h2293, h2392, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h2292, h2391, hlam]
          · linarith only [h0, h1834, h2293, hlam]
        · linarith only [h0, h1833, h2292, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2453 | h2453
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2454 | h2454
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2455 | h2455
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2456 | h2456
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2457 | h2457
              · linarith only [h1833, h1834, h2457, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2459 | h2459
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2460 | h2460
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2461 | h2461
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2462 | h2462
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2463 | h2463
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2464 | h2464
                          · linarith only [h1833, h2457, h2464, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2466 | h2466
                            · linarith only [h1833, h1834, h2464, h2466, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · linarith only [h1833, h1834, h2459, h2464, h2466, hc13, hc34, hlam, hphi]
                        · linarith only [h0, h2453, h2463, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h1833, h2455, h2459, h2462, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                    · linarith only [h0, h1833, h2459, h2461, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h1834, h2453, h2460, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2473 | h2473
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2474 | h2474
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2475 | h2475
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2476 | h2476
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2477 | h2477
                          · linarith only [h1833, h2457, h2477, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2479 | h2479
                            · linarith only [h1833, h2459, h2479, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2481 | h2481
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2482 | h2482
                                · linarith only [h1833, h1834, h2459, h2474, h2477, h2482, hc01, hc35, hlam, hphi, ht12, ht23]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2484 | h2484
                                  · linarith only [h1833, h1834, h2474, h2477, h2484, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2486 | h2486
                                    · linarith only [h2455, h2486, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                    · linarith only [h1834, h2453, h2477, h2481, h2482, h2486, hc23, hc34, hlam, hphi]
                              · linarith only [h1834, h2453, h2476, h2481, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                        · linarith only [h0, h2453, h2476, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h2453, h2475, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h2453, h2474, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h1834, h2453, h2473, hlam]
            · linarith only [h0, h2453, h2456, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2495 | h2495
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2496 | h2496
              · linarith only [h0, h1833, h2455, h2496, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2498 | h2498
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2499 | h2499
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2500 | h2500
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2501 | h2501
                      · linarith only [h2455, h2495, h2501, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h1833, h2498, h2501, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h1833, h2498, h2500, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h1833, h2455, h2498, h2499, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2506 | h2506
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2507 | h2507
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2508 | h2508
                      · linarith only [h0, h2453, h2455, h2508, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                      · linarith only [h0, h2453, h2508, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h2453, h2507, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h2453, h2455, h2506, hlam]
            · linarith only [h0, h2453, h2495, hlam]
        · linarith only [h0, h1833, h2454, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2515 | h2515
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2516 | h2516
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2517 | h2517
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2518 | h2518
              · linarith only [h1833, h1834, h2518, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2520 | h2520
                · linarith only [h1833, h2453, h2520, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2522 | h2522
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2523 | h2523
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2524 | h2524
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2525 | h2525
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2526 | h2526
                          · linarith only [h1833, h2518, h2526, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2528 | h2528
                            · linarith only [h1833, h2453, h2520, h2528, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2530 | h2530
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2531 | h2531
                                · linarith only [h2453, h2515, h2526, h2530, h2531, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2533 | h2533
                                  · linarith only [h1833, h2453, h2523, h2528, h2533, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2535 | h2535
                                    · linarith only [h2516, h2535, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2537 | h2537
                                      · rcases h0bigk with h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c | h2538c
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [hlam, p2538_0]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h0, hlam, p2538_1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h2453, h2526, h2530, hc03, hc34, hlam, hphi, p2538_1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h1834, hlam, p2538_1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h2453, hlam, p2538_1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h1833, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2538_1, u0elo1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [hlam, p2538_0]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          rcases p2538_3 (m.d 0 1) (by simp) with h2546 | h2546
                                          · linarith only [h0, h2546, hlam]
                                          · linarith only [h1833, h2546, hlam]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h2522, h2531, h2535, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2538_1, u0elo1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h1833, h2453, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2538_1, u0elo1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h1833, hlam, p2538_1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h2515, hlam, p2538_1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [hlam, p2538_0]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h2518, hlam, p2538_1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h2520, hlam, p2538_1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h1833, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2538_1, u0elo3]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h2516, hlam, p2538_0]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          rcases p2538_3 (m.d 0 1) (by simp) with h2558 | h2558
                                          · linarith only [h1834, h2558, hlam]
                                          · linarith only [h1833, h2558, hlam]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [hlam, p2538_0]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h2516, h2522, h2531, h2535, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2538_1, u0elo1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h1833, h2523, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2538_1, u0elo4]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h2517, hlam, p2538_1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          rcases p2538_3 (m.d 0 1) (by simp) with h2565 | h2565
                                          · linarith only [h2453, h2565, hlam]
                                          · linarith only [h1833, h2565, hlam]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [h2522, hlam, p2538_1]
                                        · have p2538_0 := h2538c.1
                                          have p2538_1 := h2538c.2.1
                                          have p2538_2 := h2538c.2.2.1
                                          have p2538_3 := h2538c.2.2.2
                                          linarith only [hlam, p2538_0]
                                      · linarith only [h1833, h1834, h2523, h2526, h2537, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h1834, h2522, h2530, hlam]
                        · linarith only [h0, h2517, h2525, hlam]
                      · linarith only [h0, h2516, h2524, hlam]
                    · linarith only [h0, h2515, h2523, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2575 | h2575
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2576 | h2576
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2577 | h2577
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2578 | h2578
                          · linarith only [h1833, h1834, h2522, h2578, hc34, hc45, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2580 | h2580
                            · linarith only [h1833, h1834, h2522, h2580, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2582 | h2582
                              · linarith only [h1833, h1834, h2522, h2575, h2578, h2582, hc23, hc34, hlam, hphi]
                              · linarith only [h1833, h1834, h2575, h2582, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h1833, h1834, h2517, h2575, h2576, h2577, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1833, h2516, h2575, h2576, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h2515, h2575, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2588 | h2588
              · linarith only [h1833, h1834, h2588, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2590 | h2590
                · linarith only [h1833, h2453, h2590, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2592 | h2592
                  · linarith only [h2516, h2517, h2592, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2594 | h2594
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2595 | h2595
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2596 | h2596
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2597 | h2597
                          · linarith only [h1833, h1834, h2516, h2517, h2588, h2596, h2597, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2599 | h2599
                            · linarith only [h1833, h1834, h2516, h2517, h2590, h2599, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2601 | h2601
                              · linarith only [h1833, h1834, h2592, h2597, h2601, hc13, hc34, hlam, hphi]
                              · linarith only [h1833, h1834, h2594, h2601, hc23, hc45, hlam, hphi, ht34]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2604 | h2604
                          · linarith only [h0, h1833, h2596, h2604, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2606 | h2606
                            · linarith only [h1833, h1834, h2595, h2596, h2606, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2608 | h2608
                              · linarith only [h1834, h2592, h2595, h2596, h2608, hc01, hc25, hlam, hphi, ht12]
                              · linarith only [h1833, h1834, h2594, h2608, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1833, h2516, h2594, h2595, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h2515, h2594, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2613 | h2613
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2614 | h2614
              · linarith only [h0, h1833, h2516, h2614, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2616 | h2616
                · linarith only [h1833, h2453, h2616, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2618 | h2618
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2619 | h2619
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2620 | h2620
                      · linarith only [h2516, h2613, h2620, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2622 | h2622
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2623 | h2623
                          · linarith only [h1833, h2453, h2614, h2620, h2622, h2623, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2625 | h2625
                            · linarith only [h1833, h2453, h2616, h2620, h2622, h2625, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2627 | h2627
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2628 | h2628
                                · linarith only [h2453, h2515, h2620, h2622, h2623, h2628, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h1833, h2453, h2619, h2620, h2622, h2628, hc23, hc34, hlam, hphi]
                              · linarith only [h1833, h2453, h2618, h2619, h2620, h2622, h2627, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                        · linarith only [h0, h2613, h2622, hlam]
                    · linarith only [h0, h2515, h2619, hlam]
                  · linarith only [h2516, h2613, h2618, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2635 | h2635
              · linarith only [h0, h1833, h2516, h2635, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2637 | h2637
                · linarith only [h0, h1833, h2613, h2637, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2639 | h2639
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2640 | h2640
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2641 | h2641
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2642 | h2642
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2643 | h2643
                          · linarith only [h1833, h2635, h2639, h2643, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2645 | h2645
                            · linarith only [h0, h1833, h2516, h2637, h2641, h2645, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2647 | h2647
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2648 | h2648
                                · linarith only [h0, h1833, h2516, h2640, h2641, h2643, h2648, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h2650 | h2650
                                  · linarith only [h0, h1833, h2613, h2640, h2642, h2645, h2650, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2652 | h2652
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2653 | h2653
                                      · rcases h0bigk with h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [hlam, p2654_0]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h0, hlam, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h0, h1833, h2613, h2640, h2641, h2652, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h1834, hlam, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h2453, hlam, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h2613, h2641, h2652, hc01, hc12, hlam, hphi, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [hlam, p2654_0]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h1833, h2613, h2640, h2641, h2652, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h2516, hlam, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h2613, hlam, p2654_0]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h1833, hlam, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h2515, hlam, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [hlam, p2654_0]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h2635, hlam, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h2637, hlam, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h1833, h2516, h2640, h2641, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h0, h1833, h2516, h2640, h2641, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          rcases p2654_3 (m.d 0 1) (by simp) with h2672 | h2672
                                          · linarith only [h1834, h2672, hlam]
                                          · linarith only [h1833, h2672, hlam]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [hlam, p2654_0]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h0, h1833, h2516, h2613, h2640, h2641, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h1833, h2640, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2654_1, u0elo4]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h0, h1833, h2613, h2640, h2641, h2652, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          rcases p2654_3 (m.d 0 1) (by simp) with h2679 | h2679
                                          · linarith only [h2453, h2679, hlam]
                                          · linarith only [h1833, h2679, hlam]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [h2639, hlam, p2654_1]
                                        · have p2654_0 := h2654c.1
                                          have p2654_1 := h2654c.2.1
                                          have p2654_2 := h2654c.2.2.1
                                          have p2654_3 := h2654c.2.2.2
                                          linarith only [hlam, p2654_0]
                                      · linarith only [h1833, h1834, h2640, h2643, h2653, hc23, hc45, hlam, hphi, ht34]
                                    · linarith only [h2516, h2639, h2652, hlam]
                              · linarith only [h1833, h1834, h2516, h2639, h2640, h2641, h2647, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h2516, h2641, h2642, hc02, hc25, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2688 | h2688
                        · linarith only [h0, h1833, h2613, h2640, h2641, h2688, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2690 | h2690
                          · linarith only [h1833, h2635, h2639, h2690, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2692 | h2692
                            · linarith only [h0, h1833, h2641, h2692, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2694 | h2694
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h2695 | h2695
                                · linarith only [h0, h1833, h2640, h2688, h2690, h2694, h2695, hlam]
                                · linarith only [h0, h1833, h2640, h2641, h2695, hc23, hc34, hlam, hphi]
                              · linarith only [h1833, h1834, h2639, h2640, h2694, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1833, h2515, h2640, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2700 | h2700
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2701 | h2701
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2702 | h2702
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2703 | h2703
                          · linarith only [h1833, h1834, h2639, h2703, hc34, hc45, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2705 | h2705
                            · linarith only [h0, h1833, h2613, h2702, h2705, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2707 | h2707
                              · linarith only [h0, h1833, h2516, h2639, h2703, h2707, hc13, hc34, hlam, hphi]
                              · linarith only [h1833, h1834, h2700, h2707, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h1833, h2516, h2700, h2701, h2702, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2711 | h2711
                        · linarith only [h0, h1833, h2613, h2700, h2701, h2711, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2713 | h2713
                          · linarith only [h0, h1833, h2701, h2713, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2715 | h2715
                            · linarith only [h0, h1833, h2637, h2701, h2715, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h2717 | h2717
                              · linarith only [h0, h1833, h2516, h2639, h2700, h2713, h2717, hc23, hc34, hlam, hphi]
                              · linarith only [h1833, h1834, h2700, h2717, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h2515, h2700, hlam]
        · linarith only [h0, h1833, h2515, hlam]
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1 m hb0 hb2 hb3 hb5 h0 h1833

end R2N4
