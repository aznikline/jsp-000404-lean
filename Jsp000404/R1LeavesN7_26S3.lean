import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_26S0
import Jsp000404.R1LeavesN7_26S1
import Jsp000404.R1LeavesN7_26S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h883 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1033 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1100 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1101 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1102 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 1 2 3 (by decide) (by decide) with h1827 | h1827
  · linarith only [h0, h1101, h1827, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1829 | h1829
    · linarith only [h0, h1829, h883, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1831 | h1831
      · linarith only [h0, h1033, h1102, h1831, h883, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1833 | h1833
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1834 | h1834
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1835 | h1835
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1836 | h1836
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1837 | h1837
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1838 | h1838
                  · linarith only [h1, h1102, h1833, h1838, h883, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h0bigk with h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      rcases p1840_3 (m.d 0 1) (by simp) with h1842 | h1842
                      · rcases p1840_3 (m.d 0 2) (by simp) with h1843 | h1843
                        · linarith only [h0, h1843, hlam]
                        · rcases p1840_3 (m.d 0 3) (by simp) with h1845 | h1845
                          · linarith only [h1, h1845, hlam]
                          · linarith only [h1845, h4, hlam]
                      · linarith only [h0, h1842, hlam]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h1100, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1840_1, u3ehi3]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      rcases p1840_3 (m.d 0 1) (by simp) with h1850 | h1850
                      · rcases p1840_3 (m.d 0 2) (by simp) with h1851 | h1851
                        · linarith only [h0, h1851, hlam]
                        · rcases p1840_3 (m.d 0 3) (by simp) with h1853 | h1853
                          · linarith only [h1, h1853, hlam]
                          · linarith only [h1100, h1853, hlam]
                      · linarith only [h1850, h2, hlam]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      rcases p1840_3 (m.d 0 1) (by simp) with h1857 | h1857
                      · rcases p1840_3 (m.d 0 2) (by simp) with h1858 | h1858
                        · linarith only [h0, h1858, hlam]
                        · rcases p1840_3 (m.d 0 3) (by simp) with h1860 | h1860
                          · linarith only [h1, h1860, hlam]
                          · linarith only [h1101, h1860, hlam]
                      · linarith only [h1857, h3, hlam]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h0, hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h4, hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h883, hlam, p1840_1]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h1033, hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h1, hlam, p1840_1]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      rcases p1840_3 (m.d 0 1) (by simp) with h1870 | h1870
                      · rcases p1840_3 (m.d 0 2) (by simp) with h1871 | h1871
                        · linarith only [h1871, h4, hlam]
                        · rcases p1840_3 (m.d 0 3) (by simp) with h1873 | h1873
                          · rcases p1840_3 (m.d 0 4) (by simp) with h1874 | h1874
                            · linarith only [h1100, h1874, hlam]
                            · linarith only [h1874, h883, hlam]
                          · linarith only [h1873, h4, hlam]
                      · linarith only [h0, h1870, hlam]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      rcases p1840_3 (m.d 0 1) (by simp) with h1880 | h1880
                      · rcases p1840_3 (m.d 0 2) (by simp) with h1881 | h1881
                        · linarith only [h1881, h4, hlam]
                        · rcases p1840_3 (m.d 0 3) (by simp) with h1883 | h1883
                          · rcases p1840_3 (m.d 0 4) (by simp) with h1884 | h1884
                            · linarith only [h1100, h1884, hlam]
                            · rcases p1840_3 (m.d 0 5) (by simp) with h1886 | h1886
                              · linarith only [h1101, h1886, hlam]
                              · linarith only [h1102, h1886, hlam]
                          · linarith only [h1100, h1883, hlam]
                      · linarith only [h1880, h2, hlam]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      rcases p1840_3 (m.d 0 1) (by simp) with h1891 | h1891
                      · rcases p1840_3 (m.d 0 2) (by simp) with h1892 | h1892
                        · linarith only [h1892, h4, hlam]
                        · rcases p1840_3 (m.d 0 3) (by simp) with h1894 | h1894
                          · rcases p1840_3 (m.d 0 4) (by simp) with h1895 | h1895
                            · linarith only [h1100, h1895, hlam]
                            · rcases p1840_3 (m.d 0 5) (by simp) with h1897 | h1897
                              · linarith only [h1101, h1897, hlam]
                              · rcases h2bigk with h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h4, hc12, hc23, hlam, hphi, p1899_1]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h4, hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h883, hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h1033, hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h0, hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h1827, hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h1829, hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h1831, hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  rcases p1899_3 (m.d 0 2) (by simp) with h1910 | h1910
                                  · linarith only [h1910, hlam, p1899_0]
                                  · rcases p1899_3 (m.d 1 2) (by simp) with h1912 | h1912
                                    · linarith only [h1827, h1912, hlam]
                                    · rcases p1899_3 (m.d 2 3) (by simp) with h1914 | h1914
                                      · rcases p1899_3 (m.d 2 4) (by simp) with h1915 | h1915
                                        · linarith only [h1835, h1915, hlam]
                                        · linarith only [h1915, h883, hlam]
                                      · linarith only [h1914, hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  rcases p1899_3 (m.d 0 2) (by simp) with h1919 | h1919
                                  · linarith only [h1919, h4, hlam]
                                  · linarith only [h0, h1919, hlam]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h1102, h1833, h1837, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1899_1, u3ehi3]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h1102, h1833, h1837, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1899_1, u3ehi3]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  rcases p1899_3 (m.d 0 2) (by simp) with h1925 | h1925
                                  · linarith only [h1925, hlam, p1899_0]
                                  · rcases p1899_3 (m.d 1 2) (by simp) with h1927 | h1927
                                    · linarith only [h1829, h1927, hlam]
                                    · rcases p1899_3 (m.d 2 3) (by simp) with h1929 | h1929
                                      · rcases p1899_3 (m.d 2 4) (by simp) with h1930 | h1930
                                        · rcases p1899_3 (m.d 2 5) (by simp) with h1931 | h1931
                                          · linarith only [h1837, h1931, hlam]
                                          · linarith only [h1033, h1931, hlam]
                                        · linarith only [h1930, hlam, p1899_0]
                                      · linarith only [h1929, h4, hlam]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  rcases p1899_3 (m.d 0 2) (by simp) with h1936 | h1936
                                  · linarith only [h1936, h883, hlam]
                                  · linarith only [h0, h1936, hlam]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h1835, hlam, p1899_1]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h1102, h1833, h1837, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1899_1, u3ehi3]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  rcases p1899_3 (m.d 0 2) (by simp) with h1942 | h1942
                                  · linarith only [h1942, hlam, p1899_0]
                                  · rcases p1899_3 (m.d 1 2) (by simp) with h1944 | h1944
                                    · linarith only [h1831, h1944, hlam]
                                    · rcases p1899_3 (m.d 2 3) (by simp) with h1946 | h1946
                                      · rcases p1899_3 (m.d 2 4) (by simp) with h1947 | h1947
                                        · rcases p1899_3 (m.d 2 5) (by simp) with h1948 | h1948
                                          · rcases h3bigk with h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1834, h1838, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi3]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h4, hlam, p1949_1]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              rcases p1949_3 (m.d 0 3) (by simp) with h1953 | h1953
                                              · rcases p1949_3 (m.d 1 3) (by simp) with h1954 | h1954
                                                · linarith only [h1, h1954, hlam]
                                                · linarith only [h1833, h1954, hlam]
                                              · linarith only [h1953, hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              rcases p1949_3 (m.d 0 3) (by simp) with h1958 | h1958
                                              · rcases p1949_3 (m.d 1 3) (by simp) with h1959 | h1959
                                                · linarith only [h1, h1959, hlam]
                                                · linarith only [h1834, h1959, hlam]
                                              · linarith only [h1958, hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1, hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1827, hlam, p1949_1]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi3]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1, h1838, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi3]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1100, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1949_1, u3ehi3]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1833, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1949_1, u3ehi3]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              rcases p1949_3 (m.d 0 3) (by simp) with h1971 | h1971
                                              · linarith only [h1971, h4, hlam]
                                              · linarith only [h1100, h1971, hlam]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              rcases p1949_3 (m.d 0 3) (by simp) with h1974 | h1974
                                              · linarith only [h1974, h4, hlam]
                                              · linarith only [h1101, h1974, hlam]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1100, hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1833, hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1835, hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1838, hlam, p1949_1]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1101, hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1834, hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1836, hlam, p1949_0]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [h1834, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1949_1, u3ehi3]
                                            · have p1949_0 := h1949c.1
                                              have p1949_1 := h1949c.2.1
                                              have p1949_2 := h1949c.2.2.1
                                              have p1949_3 := h1949c.2.2.2
                                              linarith only [hlam, p1949_0]
                                          · linarith only [h1948, hlam, p1899_0]
                                        · linarith only [h1947, h883, hlam]
                                      · linarith only [h1946, h4, hlam]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  rcases p1899_3 (m.d 0 2) (by simp) with h1990 | h1990
                                  · linarith only [h1033, h1990, hlam]
                                  · linarith only [h0, h1990, hlam]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h1836, hlam, p1899_1]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [h1837, hlam, p1899_0]
                                · have p1899_0 := h1899c.1
                                  have p1899_1 := h1899c.2.1
                                  have p1899_2 := h1899c.2.2.1
                                  have p1899_3 := h1899c.2.2.2
                                  linarith only [hlam, p1899_0]
                          · linarith only [h1101, h1894, hlam]
                      · linarith only [h1891, h3, hlam]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h2, hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h0, h1102, hc12, hc45, hlam, hphi, ht23, ht34, p1840_1]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h1100, hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h1102, hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h3, hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h0, h1102, h1835, h1837, hc12, hc23, hlam, hphi, p1840_1]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h1101, hlam, p1840_0]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [h1102, h1833, h1835, h1837, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1840_1, u3ehi3]
                    · have p1840_0 := h1840c.1
                      have p1840_1 := h1840c.2.1
                      have p1840_2 := h1840c.2.2.1
                      have p1840_3 := h1840c.2.2.2
                      linarith only [hlam, p1840_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2008 | h2008
                  · linarith only [h0, h1837, h2008, h883, hc12, hc34, hlam, hphi, ht23]
                  · rcases h0bigk with h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c | h2010c
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      rcases p2010_3 (m.d 0 1) (by simp) with h2012 | h2012
                      · rcases p2010_3 (m.d 0 2) (by simp) with h2013 | h2013
                        · linarith only [h0, h2013, hlam]
                        · rcases p2010_3 (m.d 0 3) (by simp) with h2015 | h2015
                          · linarith only [h1, h2015, hlam]
                          · linarith only [h2015, h4, hlam]
                      · linarith only [h0, h2012, hlam]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h1, h1834, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p2010_1, u3ehi4]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      rcases p2010_3 (m.d 0 1) (by simp) with h2020 | h2020
                      · rcases p2010_3 (m.d 0 2) (by simp) with h2021 | h2021
                        · linarith only [h0, h2021, hlam]
                        · rcases p2010_3 (m.d 0 3) (by simp) with h2023 | h2023
                          · linarith only [h1, h2023, hlam]
                          · linarith only [h1100, h2023, hlam]
                      · linarith only [h2, h2020, hlam]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      rcases p2010_3 (m.d 0 1) (by simp) with h2027 | h2027
                      · rcases p2010_3 (m.d 0 2) (by simp) with h2028 | h2028
                        · linarith only [h0, h2028, hlam]
                        · rcases p2010_3 (m.d 0 3) (by simp) with h2030 | h2030
                          · linarith only [h1, h2030, hlam]
                          · linarith only [h1101, h2030, hlam]
                      · linarith only [h2027, h3, hlam]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h0, hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h4, hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h883, hlam, p2010_1]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h1033, hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h1, hlam, p2010_1]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      rcases p2010_3 (m.d 0 1) (by simp) with h2040 | h2040
                      · rcases p2010_3 (m.d 0 2) (by simp) with h2041 | h2041
                        · linarith only [h2041, h4, hlam]
                        · rcases p2010_3 (m.d 0 3) (by simp) with h2043 | h2043
                          · rcases p2010_3 (m.d 0 4) (by simp) with h2044 | h2044
                            · linarith only [h1100, h2044, hlam]
                            · linarith only [h2044, h883, hlam]
                          · linarith only [h2043, h4, hlam]
                      · linarith only [h0, h2040, hlam]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      rcases p2010_3 (m.d 0 1) (by simp) with h2050 | h2050
                      · rcases p2010_3 (m.d 0 2) (by simp) with h2051 | h2051
                        · linarith only [h2051, h4, hlam]
                        · rcases p2010_3 (m.d 0 3) (by simp) with h2053 | h2053
                          · rcases p2010_3 (m.d 0 4) (by simp) with h2054 | h2054
                            · linarith only [h1100, h2054, hlam]
                            · rcases p2010_3 (m.d 0 5) (by simp) with h2056 | h2056
                              · linarith only [h1101, h2056, hlam]
                              · linarith only [h1102, h2056, hlam]
                          · linarith only [h1100, h2053, hlam]
                      · linarith only [h2, h2050, hlam]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      rcases p2010_3 (m.d 0 1) (by simp) with h2061 | h2061
                      · rcases p2010_3 (m.d 0 2) (by simp) with h2062 | h2062
                        · linarith only [h2062, h4, hlam]
                        · rcases p2010_3 (m.d 0 3) (by simp) with h2064 | h2064
                          · rcases p2010_3 (m.d 0 4) (by simp) with h2065 | h2065
                            · linarith only [h1100, h2065, hlam]
                            · rcases p2010_3 (m.d 0 5) (by simp) with h2067 | h2067
                              · linarith only [h1101, h2067, hlam]
                              · rcases h2bigk with h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c | h2069c
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h883, hc12, hc24, hlam, hphi, p2069_1]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h4, hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h883, hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h1033, hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h0, hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h1827, hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h1829, hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h1831, hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  rcases p2069_3 (m.d 0 2) (by simp) with h2080 | h2080
                                  · linarith only [h2080, hlam, p2069_0]
                                  · rcases p2069_3 (m.d 1 2) (by simp) with h2082 | h2082
                                    · linarith only [h1827, h2082, hlam]
                                    · rcases p2069_3 (m.d 2 3) (by simp) with h2084 | h2084
                                      · rcases p2069_3 (m.d 2 4) (by simp) with h2085 | h2085
                                        · linarith only [h1835, h2085, hlam]
                                        · linarith only [h2085, h883, hlam]
                                      · linarith only [h2084, hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  rcases p2069_3 (m.d 0 2) (by simp) with h2089 | h2089
                                  · linarith only [h2089, h4, hlam]
                                  · linarith only [h0, h2089, hlam]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h883, hc02, hc23, hlam, hphi, p2069_1]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h0, h1033, hc12, hc23, hlam, hphi, p2069_1]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h0, h1102, h1833, h1837, h2, h4, hc12, hc23, hc45, hlam, hphi, ht34, p2010_1, p2069_1, u3ehi3]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h1102, h1833, h1837, h2, h4, hc12, hc23, hc45, hlam, hphi, ht34, p2010_1, p2069_1, u3ehi3]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h1835, hlam, p2069_1]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [hlam, p2069_0]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h1837, hlam, p2069_1]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  rcases p2069_3 (m.d 0 2) (by simp) with h2100 | h2100
                                  · linarith only [h2100, hlam, p2069_0]
                                  · rcases p2069_3 (m.d 1 2) (by simp) with h2102 | h2102
                                    · linarith only [h1831, h2102, hlam]
                                    · rcases p2069_3 (m.d 2 3) (by simp) with h2104 | h2104
                                      · rcases p2069_3 (m.d 2 4) (by simp) with h2105 | h2105
                                        · linarith only [h1837, h2105, hlam]
                                        · linarith only [h2105, h883, hlam]
                                      · linarith only [h2104, h4, hlam]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  rcases p2069_3 (m.d 0 2) (by simp) with h2109 | h2109
                                  · linarith only [h1033, h2109, hlam]
                                  · linarith only [h0, h2109, hlam]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h1836, hlam, p2069_1]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [h0, h883, hc12, hc25, hlam, hphi, p2069_1]
                                · have p2069_0 := h2069c.1
                                  have p2069_1 := h2069c.2.1
                                  have p2069_2 := h2069c.2.2.1
                                  have p2069_3 := h2069c.2.2.2
                                  linarith only [hlam, p2069_0]
                          · linarith only [h1101, h2064, hlam]
                      · linarith only [h2061, h3, hlam]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h2, hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h0, h1102, hc12, hc45, hlam, hphi, ht23, ht34, p2010_1]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h1100, hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h1102, hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h3, hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      rcases p2010_3 (m.d 0 1) (by simp) with h2123 | h2123
                      · rcases p2010_3 (m.d 0 2) (by simp) with h2124 | h2124
                        · linarith only [h1033, h2124, hlam]
                        · rcases p2010_3 (m.d 0 3) (by simp) with h2126 | h2126
                          · rcases p2010_3 (m.d 0 4) (by simp) with h2127 | h2127
                            · linarith only [h1102, h2127, hlam]
                            · linarith only [h2127, h883, hlam]
                          · linarith only [h2126, h4, hlam]
                      · linarith only [h0, h2123, hlam]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h1101, hlam, p2010_0]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [h1033, h1100, h1837, hc45, hlam, hphi, ht34, p2010_1, u3ehi3]
                    · have p2010_0 := h2010c.1
                      have p2010_1 := h2010c.2.1
                      have p2010_2 := h2010c.2.2.1
                      have p2010_3 := h2010c.2.2.2
                      linarith only [hlam, p2010_0]
              · linarith only [h1, h1834, h1836, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · linarith only [h1, h1834, h1835, h4, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1833, h1834, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1100, h1102, h1833, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h883 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1033 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1100 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1101 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 4 5 (by decide) (by decide) with h1102 | h1102
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4 h883 h1033 h1100 h1101 h1102
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4 h883 h1033 h1100 h1101 h1102

set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h883 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1033 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1100 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1101 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  linarith only [h1100, h1101, hc35, hlam, hphi, u3ehi3]

set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h883 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1033 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1100 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 3 5 (by decide) (by decide) with h1101 | h1101
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4 h883 h1033 h1100 h1101
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4 h883 h1033 h1100 h1101

set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h883 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1033 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1100 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 3 5 (by decide) (by decide) with h2140 | h2140
  · linarith only [h1100, h2140, hc34, hlam, hphi, u3ehi4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2142 | h2142
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2143 | h2143
      · linarith only [h0, h2143, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2145 | h2145
        · linarith only [h0, h2145, h883, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2147 | h2147
          · linarith only [h0, h1033, h2147, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2149 | h2149
            · linarith only [h1, h1100, h2149, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2151 | h2151
              · linarith only [h1, h2140, h2151, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2153 | h2153
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2154 | h2154
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2155 | h2155
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2156 | h2156
                      · rcases h0bigk with h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          rcases p2157_3 (m.d 0 1) (by simp) with h2159 | h2159
                          · rcases p2157_3 (m.d 0 2) (by simp) with h2160 | h2160
                            · linarith only [h0, h2160, hlam]
                            · rcases p2157_3 (m.d 0 3) (by simp) with h2162 | h2162
                              · linarith only [h1, h2162, hlam]
                              · linarith only [h2162, h4, hlam]
                          · linarith only [h0, h2159, hlam]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          rcases p2157_3 (m.d 0 1) (by simp) with h2166 | h2166
                          · rcases p2157_3 (m.d 0 2) (by simp) with h2167 | h2167
                            · linarith only [h0, h2167, hlam]
                            · rcases p2157_3 (m.d 0 3) (by simp) with h2169 | h2169
                              · linarith only [h1, h2169, hlam]
                              · rcases p2157_3 (m.d 0 4) (by simp) with h2171 | h2171
                                · linarith only [h2, h2171, hlam]
                                · linarith only [h1100, h2171, hlam]
                          · linarith only [h1, h2166, hlam]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          rcases p2157_3 (m.d 0 1) (by simp) with h2175 | h2175
                          · rcases p2157_3 (m.d 0 2) (by simp) with h2176 | h2176
                            · linarith only [h0, h2176, hlam]
                            · rcases p2157_3 (m.d 0 3) (by simp) with h2178 | h2178
                              · linarith only [h1, h2178, hlam]
                              · rcases p2157_3 (m.d 0 4) (by simp) with h2180 | h2180
                                · linarith only [h2, h2180, hlam]
                                · rcases p2157_3 (m.d 0 5) (by simp) with h2182 | h2182
                                  · linarith only [h2182, h3, hlam]
                                  · rcases h2bigk with h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c | h2184c
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h2140, h2153, h2156, h4, hc12, hc23, hlam, hphi, p2184_1]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h4, hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h883, hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h1033, hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h0, hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h2143, hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h2145, hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h2147, hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      rcases p2184_3 (m.d 0 2) (by simp) with h2195 | h2195
                                      · linarith only [h2195, hlam, p2184_0]
                                      · rcases p2184_3 (m.d 1 2) (by simp) with h2197 | h2197
                                        · linarith only [h2143, h2197, hlam]
                                        · rcases p2184_3 (m.d 2 3) (by simp) with h2199 | h2199
                                          · rcases p2184_3 (m.d 2 4) (by simp) with h2200 | h2200
                                            · linarith only [h2153, h2200, hlam]
                                            · linarith only [h2200, h883, hlam]
                                          · linarith only [h2199, hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      rcases p2184_3 (m.d 0 2) (by simp) with h2204 | h2204
                                      · linarith only [h2204, h4, hlam]
                                      · linarith only [h0, h2204, hlam]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h2140, h2154, h2155, h4, hc02, hc23, hlam, hphi, p2184_1]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h1, h2140, h2154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2184_1, u3ehi1]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      rcases p2184_3 (m.d 0 2) (by simp) with h2210 | h2210
                                      · linarith only [h2210, hlam, p2184_0]
                                      · rcases p2184_3 (m.d 1 2) (by simp) with h2212 | h2212
                                        · linarith only [h2145, h2212, hlam]
                                        · rcases p2184_3 (m.d 2 3) (by simp) with h2214 | h2214
                                          · rcases p2184_3 (m.d 2 4) (by simp) with h2215 | h2215
                                            · rcases p2184_3 (m.d 2 5) (by simp) with h2216 | h2216
                                              · linarith only [h2155, h2216, hlam]
                                              · linarith only [h1033, h2216, hlam]
                                            · linarith only [h2215, hlam, p2184_0]
                                          · linarith only [h2214, h4, hlam]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      rcases p2184_3 (m.d 0 2) (by simp) with h2221 | h2221
                                      · linarith only [h2221, h883, hlam]
                                      · linarith only [h0, h2221, hlam]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h2153, hlam, p2184_1]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h1, h2140, h2154, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2184_1, u3ehi1]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      rcases p2184_3 (m.d 0 2) (by simp) with h2227 | h2227
                                      · linarith only [h2227, hlam, p2184_0]
                                      · rcases p2184_3 (m.d 1 2) (by simp) with h2229 | h2229
                                        · linarith only [h2147, h2229, hlam]
                                        · rcases p2184_3 (m.d 2 3) (by simp) with h2231 | h2231
                                          · rcases p2184_3 (m.d 2 4) (by simp) with h2232 | h2232
                                            · rcases p2184_3 (m.d 2 5) (by simp) with h2233 | h2233
                                              · rcases h3bigk with h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h2140, h2156, hc34, hlam, hphi, p2234_1, u3ehi1]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h4, hlam, p2234_1]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h1100, hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h2140, hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h1, hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h2143, hlam, p2234_1]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h2149, hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h2151, hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  rcases p2234_3 (m.d 0 3) (by simp) with h2245 | h2245
                                                  · linarith only [h2245, h4, hlam]
                                                  · rcases p2234_3 (m.d 1 3) (by simp) with h2247 | h2247
                                                    · linarith only [h2143, h2247, hlam]
                                                    · rcases p2234_3 (m.d 2 3) (by simp) with h2249 | h2249
                                                      · rcases p2234_3 (m.d 3 4) (by simp) with h2250 | h2250
                                                        · linarith only [h2153, h2250, hlam]
                                                        · linarith only [h1100, h2250, hlam]
                                                      · linarith only [h2249, h4, hlam]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  rcases p2234_3 (m.d 0 3) (by simp) with h2254 | h2254
                                                  · linarith only [h2254, h4, hlam]
                                                  · linarith only [h1, h2254, hlam]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h2140, h2156, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2234_1, u3ehi0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h1, h2140, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2234_1, u3ehi1]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h1, hc34, hlam, hphi, p2234_1, u3ehi1]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [hc34, hlam, hphi, p2234_1, u3ehi1]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h2153, hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h1, h2140, h2153, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2234_1, u3ehi1]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h1, hc35, hlam, hphi, p2234_1, u3ehi1]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [hc35, hlam, hphi, p2234_1, u3ehi1]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h2154, hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [h2156, hlam, p2234_0]
                                                · have p2234_0 := h2234c.1
                                                  have p2234_1 := h2234c.2.1
                                                  have p2234_2 := h2234c.2.2.1
                                                  have p2234_3 := h2234c.2.2.2
                                                  linarith only [hlam, p2234_0]
                                              · linarith only [h2233, hlam, p2184_0]
                                            · linarith only [h2232, h883, hlam]
                                          · linarith only [h2231, h4, hlam]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      rcases p2184_3 (m.d 0 2) (by simp) with h2273 | h2273
                                      · linarith only [h1033, h2273, hlam]
                                      · linarith only [h0, h2273, hlam]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h2154, hlam, p2184_1]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [h2155, hlam, p2184_0]
                                    · have p2184_0 := h2184c.1
                                      have p2184_1 := h2184c.2.1
                                      have p2184_2 := h2184c.2.2.1
                                      have p2184_3 := h2184c.2.2.2
                                      linarith only [hlam, p2184_0]
                          · linarith only [h2, h2175, hlam]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          rcases p2157_3 (m.d 0 1) (by simp) with h2280 | h2280
                          · rcases p2157_3 (m.d 0 2) (by simp) with h2281 | h2281
                            · linarith only [h0, h2281, hlam]
                            · rcases p2157_3 (m.d 0 3) (by simp) with h2283 | h2283
                              · linarith only [h1, h2283, hlam]
                              · rcases p2157_3 (m.d 0 4) (by simp) with h2285 | h2285
                                · linarith only [h2, h2285, hlam]
                                · linarith only [h2142, h2285, hlam]
                          · linarith only [h2280, h3, hlam]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h0, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h4, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h883, hlam, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1033, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1, hlam, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h0, h1100, h2153, hc12, hc23, hlam, hphi, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1100, hlam, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h2140, hlam, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h2, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h0, h1100, h2153, hc12, hc23, hlam, hphi, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1100, h2153, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2157_1, u3ehi0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h0, h1033, h1100, h2153, hc12, hc23, hlam, hphi, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h3, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h0, h2140, h2153, h2156, hc12, hc23, hlam, hphi, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1, h2140, h2153, h2156, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2157_1, u3ehi1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h2142, hlam, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [hlam, p2157_0]
                      · linarith only [h1100, h2142, h2156, hlam]
                    · linarith only [h0, h1100, h2142, h2153, h2155, h883, hc12, hc23, hlam, hphi]
                  · linarith only [h2153, h2154, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2312 | h2312
                  · linarith only [h2153, h2312, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2314 | h2314
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2315 | h2315
                      · rcases h0bigk with h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [hlam, p2316_0]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          rcases p2316_3 (m.d 0 1) (by simp) with h2318 | h2318
                          · rcases p2316_3 (m.d 0 2) (by simp) with h2319 | h2319
                            · linarith only [h0, h2319, hlam]
                            · rcases p2316_3 (m.d 0 3) (by simp) with h2321 | h2321
                              · linarith only [h1, h2321, hlam]
                              · linarith only [h2321, h4, hlam]
                          · linarith only [h0, h2318, hlam]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          rcases p2316_3 (m.d 0 1) (by simp) with h2325 | h2325
                          · rcases p2316_3 (m.d 0 2) (by simp) with h2326 | h2326
                            · linarith only [h0, h2326, hlam]
                            · rcases p2316_3 (m.d 0 3) (by simp) with h2328 | h2328
                              · linarith only [h1, h2328, hlam]
                              · rcases p2316_3 (m.d 0 4) (by simp) with h2330 | h2330
                                · linarith only [h2, h2330, hlam]
                                · linarith only [h1100, h2330, hlam]
                          · linarith only [h1, h2325, hlam]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          rcases p2316_3 (m.d 0 1) (by simp) with h2334 | h2334
                          · rcases p2316_3 (m.d 0 2) (by simp) with h2335 | h2335
                            · linarith only [h0, h2335, hlam]
                            · rcases p2316_3 (m.d 0 3) (by simp) with h2337 | h2337
                              · linarith only [h1, h2337, hlam]
                              · rcases p2316_3 (m.d 0 4) (by simp) with h2339 | h2339
                                · linarith only [h2, h2339, hlam]
                                · rcases p2316_3 (m.d 0 5) (by simp) with h2341 | h2341
                                  · linarith only [h2341, h3, hlam]
                                  · rcases h2bigk with h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h2312, h2315, h4, hc12, hc34, hlam, hphi, ht23, p2343_1]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h4, hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h883, hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h1033, hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h0, hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h2143, hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h2145, hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h2147, hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h2312, h2315, hc02, hc34, hlam, hphi, ht23, p2343_1]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h2312, h2315, hc12, hc34, hlam, hphi, ht23, p2343_1]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h2153, hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h2312, hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      rcases p2343_3 (m.d 0 2) (by simp) with h2359 | h2359
                                      · linarith only [h2359, hlam, p2343_0]
                                      · rcases p2343_3 (m.d 1 2) (by simp) with h2361 | h2361
                                        · linarith only [h2145, h2361, hlam]
                                        · rcases p2343_3 (m.d 2 3) (by simp) with h2363 | h2363
                                          · linarith only [h2153, h2363, hlam]
                                          · linarith only [h2363, h4, hlam]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      rcases p2343_3 (m.d 0 2) (by simp) with h2366 | h2366
                                      · linarith only [h2366, h883, hlam]
                                      · linarith only [h0, h2366, hlam]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h2153, hc34, hlam, hphi, p2343_1, u3ehi2]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h0, h1033, h2153, hc12, hc34, hlam, hphi, ht23, p2343_1]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      rcases p2343_3 (m.d 0 2) (by simp) with h2372 | h2372
                                      · linarith only [h2372, hlam, p2343_0]
                                      · rcases p2343_3 (m.d 1 2) (by simp) with h2374 | h2374
                                        · linarith only [h2147, h2374, hlam]
                                        · rcases p2343_3 (m.d 2 3) (by simp) with h2376 | h2376
                                          · linarith only [h2312, h2376, hlam]
                                          · linarith only [h2376, h4, hlam]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      rcases p2343_3 (m.d 0 2) (by simp) with h2379 | h2379
                                      · linarith only [h1033, h2379, hlam]
                                      · linarith only [h0, h2379, hlam]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p2343_1]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [h2314, hlam, p2343_0]
                                    · have p2343_0 := h2343c.1
                                      have p2343_1 := h2343c.2.1
                                      have p2343_2 := h2343c.2.2.1
                                      have p2343_3 := h2343c.2.2.2
                                      linarith only [hlam, p2343_0]
                          · linarith only [h2, h2334, hlam]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          rcases p2316_3 (m.d 0 1) (by simp) with h2386 | h2386
                          · rcases p2316_3 (m.d 0 2) (by simp) with h2387 | h2387
                            · linarith only [h0, h2387, hlam]
                            · rcases p2316_3 (m.d 0 3) (by simp) with h2389 | h2389
                              · linarith only [h1, h2389, hlam]
                              · rcases p2316_3 (m.d 0 4) (by simp) with h2391 | h2391
                                · linarith only [h2, h2391, hlam]
                                · linarith only [h2142, h2391, hlam]
                          · linarith only [h2386, h3, hlam]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h0, hlam, p2316_0]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [hlam, p2316_0]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h4, hlam, p2316_0]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h883, hlam, p2316_1]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h1033, hlam, p2316_0]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h1, hlam, p2316_1]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h0, h1100, hc12, hc34, hlam, hphi, ht23, p2316_1]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [hlam, p2316_0]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h1100, hlam, p2316_1]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h2140, hlam, p2316_1]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h2, hlam, p2316_0]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          rcases p2316_3 (m.d 0 1) (by simp) with h2406 | h2406
                          · rcases p2316_3 (m.d 0 2) (by simp) with h2407 | h2407
                            · linarith only [h2407, h883, hlam]
                            · rcases p2316_3 (m.d 0 3) (by simp) with h2409 | h2409
                              · linarith only [h1100, h2409, hlam]
                              · linarith only [h2409, h4, hlam]
                          · linarith only [h0, h2406, hlam]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h1, h2153, h883, hc34, hlam, hphi, p2316_1, u3ehi1]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [hlam, p2316_0]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h1, h2140, h2153, h883, hc34, hlam, hphi, p2316_1, u3ehi1]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h3, hlam, p2316_0]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          rcases p2316_3 (m.d 0 1) (by simp) with h2417 | h2417
                          · rcases p2316_3 (m.d 0 2) (by simp) with h2418 | h2418
                            · linarith only [h1033, h2418, hlam]
                            · rcases p2316_3 (m.d 0 3) (by simp) with h2420 | h2420
                              · linarith only [h2140, h2420, hlam]
                              · linarith only [h2420, h4, hlam]
                          · linarith only [h0, h2417, hlam]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h1, h1033, h2312, h2315, hc34, hlam, hphi, p2316_1, u3ehi1]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [h2142, hlam, p2316_1]
                        · have p2316_0 := h2316c.1
                          have p2316_1 := h2316c.2.1
                          have p2316_2 := h2316c.2.2.1
                          have p2316_3 := h2316c.2.2.2
                          linarith only [hlam, p2316_0]
                      · linarith only [h2142, h2153, h2315, h883, hlam]
                    · linarith only [h2142, h2314, h883, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2429 | h2429
      · linarith only [h0, h2429, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2431 | h2431
        · linarith only [h0, h2431, h883, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2433 | h2433
          · linarith only [h0, h1033, h2433, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2435 | h2435
            · linarith only [h1, h1100, h2142, h2435, hc45, hlam, hphi, ht34, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2437 | h2437
              · linarith only [h1, h1100, h2142, h2437, hc45, hlam, hphi, ht34, u3ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2439 | h2439
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2440 | h2440
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2441 | h2441
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2442 | h2442
                      · linarith only [h1100, h2142, h2442, hc34, hlam, hphi, u3ehi0]
                      · linarith only [h1, h1100, h2439, h2441, h2442, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h1, h1100, h2439, h2441, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h1, h1100, h2439, h2440, hc35, hlam, hphi, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2447 | h2447
                  · linarith only [h2439, h2447, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2449 | h2449
                    · linarith only [h1, h1100, h2142, h2439, h2449, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2451 | h2451
                      · linarith only [h1, h1100, h2142, h2451, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h1, h1100, h2451, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h883 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1033 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 3 4 (by decide) (by decide) with h1100 | h1100
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4 h883 h1033 h1100
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4 h883 h1033 h1100

set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h883 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 5 (by decide) (by decide) with h1033 | h1033
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4 h883 h1033
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4 h883 h1033

set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 4 (by decide) (by decide) with h883 | h883
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4 h883
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4 h883

set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 h3 h4

set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 3 (by decide) (by decide) with h2454 | h2454
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2455 | h2455
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2456 | h2456
      · linarith only [h0, h2456, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2458 | h2458
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2459 | h2459
          · linarith only [h0, h2454, h2459, h3, hlam]
          · linarith only [h2458, h2459, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2462 | h2462
          · linarith only [h2458, h2462, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2464 | h2464
            · linarith only [h0, h2455, h2464, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2466 | h2466
              · linarith only [h0, h2466, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h2454, h2456, h2466, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2469 | h2469
      · linarith only [h0, h2469, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2471 | h2471
        · linarith only [h2454, h2455, h2471, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2473 | h2473
          · linarith only [h2471, h2473, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2475 | h2475
            · linarith only [h2, h2475, h3, hlam]
            · linarith only [h2454, h2455, h2475, hc45, hlam, hphi, ht34, u3ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2478 | h2478
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2479 | h2479
      · linarith only [h0, h2479, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2481 | h2481
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2482 | h2482
          · linarith only [h1, h2482, h3, hlam]
          · linarith only [h2481, h2482, hc35, hlam, hphi, u3ehi3]
        · linarith only [h2454, h2478, h2481, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2486 | h2486
      · linarith only [h2, h2478, h2486, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2488 | h2488
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2489 | h2489
          · linarith only [h1, h2489, h3, hlam]
          · linarith only [h2488, h2489, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2492 | h2492
          · linarith only [h2488, h2492, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2494 | h2494
            · linarith only [h2, h2494, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2496 | h2496
              · linarith only [h0, h2496, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2498 | h2498
                · linarith only [h0, h2478, h2498, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2500 | h2500
                  · linarith only [h0, h2486, h2500, h3, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2502 | h2502
                    · linarith only [h1, h2454, h2488, h2500, h2502, h3, hc02, hc25, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2504 | h2504
                      · linarith only [h1, h2488, h2504, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h2, h2502, h2504, h3, hc35, hlam, hphi, u3ehi1]

set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x0 m hb0 hb2 hb3 hg0 hg1 hg2 h3
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2_x1 m hb0 hb2 hb3 hg0 hg1 hg2 h3

set_option maxHeartbeats 5168000 in
set_option maxHeartbeats 5168000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s2 m hb0 hb2 hb3 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2507 | h2507
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2508 | h2508
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2509 | h2509
        · linarith only [h0, h2, h2509, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2511 | h2511
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2512 | h2512
            · linarith only [h0, h2, h2508, h2512, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2514 | h2514
              · linarith only [h2512, h2514, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2516 | h2516
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2517 | h2517
                  · linarith only [h0, h2, h2517, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h2508, h2509, h2517, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h2508, h2516, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2521 | h2521
            · linarith only [h0, h2, h2508, h2521, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2523 | h2523
              · linarith only [h2521, h2523, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2525 | h2525
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2526 | h2526
                  · linarith only [h0, h2, h2526, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h2508, h2509, h2526, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h2508, h2525, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2530 | h2530
        · linarith only [h1, h2, h2508, h2530, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2532 | h2532
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2533 | h2533
            · linarith only [h1, h2, h2533, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2535 | h2535
              · linarith only [h2533, h2535, hc34, hlam, hphi, u3ehi4]
              · linarith only [h2508, h2532, h2535, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2538 | h2538
            · linarith only [h1, h2, h2538, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2540 | h2540
              · linarith only [h2538, h2540, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2542 | h2542
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2543 | h2543
                  · linarith only [h0, h2, h2508, h2543, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2545 | h2545
                    · linarith only [h0, h2, h2530, h2545, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2547 | h2547
                      · linarith only [h1, h2, h2532, h2543, h2545, h2547, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2549 | h2549
                        · linarith only [h1, h2, h2545, h2549, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h2, h2549, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1, h2, h2542, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2553 | h2553
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2554 | h2554
        · linarith only [h0, h2, h2554, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2556 | h2556
          · linarith only [h0, h2507, h2556, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2558 | h2558
            · linarith only [h0, h2, h2553, h2558, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2560 | h2560
              · linarith only [h2558, h2560, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2562 | h2562
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2563 | h2563
                  · linarith only [h0, h2, h2563, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h2553, h2554, h2563, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h2553, h2562, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2567 | h2567
        · linarith only [h1, h2, h2553, h2567, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2569 | h2569
          · linarith only [h1, h2507, h2553, h2569, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2571 | h2571
            · linarith only [h1, h2, h2571, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2573 | h2573
              · linarith only [h2571, h2573, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2575 | h2575
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2576 | h2576
                  · linarith only [h0, h2, h2553, h2576, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2578 | h2578
                    · linarith only [h0, h2567, h2578, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2580 | h2580
                      · linarith only [h0, h2507, h2569, h2580, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2582 | h2582
                        · linarith only [h1, h2, h2553, h2571, h2578, h2582, hc02, hc24, hlam, hphi]
                        · linarith only [h1, h2, h2582, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1, h2, h2575, hc45, hlam, hphi, ht34, u3ehi1]

end R2N4
