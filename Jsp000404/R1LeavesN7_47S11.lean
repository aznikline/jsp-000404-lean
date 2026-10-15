import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_47S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1337 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1338 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1865 | h1865
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1866 | h1866
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1867 | h1867
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1868 | h1868
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1869 | h1869
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1870 | h1870
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1871 | h1871
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1872 | h1872
                · linarith only [h0, h1335, h1339, h1870, h1872, h664, hc01, hc12, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1874 | h1874
                  · linarith only [h1336, h1339, h1870, h1874, hlam]
                  · rcases h2bigk with h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h0, hlam, p1876_1]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      rcases p1876_3 (m.d 0 2) (by simp) with h1879 | h1879
                      · rcases p1876_3 (m.d 1 2) (by simp) with h1880 | h1880
                        · rcases p1876_3 (m.d 2 3) (by simp) with h1881 | h1881
                          · linarith only [h1881, hlam, p1876_0]
                          · rcases p1876_3 (m.d 2 4) (by simp) with h1883 | h1883
                            · linarith only [h1336, h1883, hlam]
                            · rcases p1876_3 (m.d 2 5) (by simp) with h1885 | h1885
                              · linarith only [h1337, h1885, hlam]
                              · rcases h4bigk with h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [hlam, p1887_0]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h664, hlam, p1887_0]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1339, h1868, h1869, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1887_1, u2ehi3]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1339, h1868, h1869, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1887_1]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1339, hlam, p1887_0]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  rcases p1887_3 (m.d 0 4) (by simp) with h1893 | h1893
                                  · linarith only [h1893, h664, hlam]
                                  · rcases p1887_3 (m.d 1 4) (by simp) with h1895 | h1895
                                    · rcases p1887_3 (m.d 2 4) (by simp) with h1896 | h1896
                                      · linarith only [h1866, h1896, hlam]
                                      · rcases p1887_3 (m.d 3 4) (by simp) with h1898 | h1898
                                        · linarith only [h1868, h1898, hlam]
                                        · rcases p1887_3 (m.d 4 5) (by simp) with h1900 | h1900
                                          · linarith only [h1869, h1900, hlam]
                                          · linarith only [h1339, h1900, hlam]
                                    · linarith only [h1895, h664, hlam]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [hlam, p1887_0]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  rcases p1887_3 (m.d 0 4) (by simp) with h1905 | h1905
                                  · linarith only [h1905, h664, hlam]
                                  · linarith only [h1336, h1905, hlam]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  rcases p1887_3 (m.d 0 4) (by simp) with h1908 | h1908
                                  · linarith only [h1908, h664, hlam]
                                  · linarith only [h1338, h1908, hlam]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1339, h664, hc01, hc14, hlam, hphi, p1887_1]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1336, hlam, p1887_1]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1866, hlam, p1887_1]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [hlam, p1887_0]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1336, h1339, hc34, hc45, hlam, hphi, p1887_1]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1872, hlam, p1887_0]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1338, hlam, p1887_1]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1868, hlam, p1887_0]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1870, hlam, p1887_0]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [hlam, p1887_0]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1874, hlam, p1887_0]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1336, hc45, hlam, hphi, ht23, ht34, p1887_1, u2ehi3]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1869, hlam, p1887_0]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [h1865, h1868, h1869, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1887_1, u2ehi3]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  rcases p1887_3 (m.d 0 4) (by simp) with h1925 | h1925
                                  · linarith only [h1339, h1925, hlam]
                                  · linarith only [h1338, h1925, hlam]
                                · have p1887_0 := h1887c.1
                                  have p1887_1 := h1887c.2.1
                                  have p1887_2 := h1887c.2.2.1
                                  have p1887_3 := h1887c.2.2.2
                                  linarith only [hlam, p1887_0]
                        · linarith only [h1865, h1880, hlam]
                      · linarith only [h1879, hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      rcases p1876_3 (m.d 0 2) (by simp) with h1931 | h1931
                      · rcases p1876_3 (m.d 1 2) (by simp) with h1932 | h1932
                        · rcases p1876_3 (m.d 2 3) (by simp) with h1933 | h1933
                          · linarith only [h1335, h1933, hlam]
                          · linarith only [h1870, h1933, hlam]
                        · linarith only [h1866, h1932, hlam]
                      · linarith only [h1931, hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      rcases p1876_3 (m.d 0 2) (by simp) with h1938 | h1938
                      · rcases p1876_3 (m.d 1 2) (by simp) with h1939 | h1939
                        · rcases p1876_3 (m.d 2 3) (by simp) with h1940 | h1940
                          · linarith only [h1335, h1940, hlam]
                          · linarith only [h1871, h1940, hlam]
                        · linarith only [h1867, h1939, hlam]
                      · linarith only [h1938, hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h1335, h1871, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1876_1, u2ehi4]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      rcases p1876_3 (m.d 0 2) (by simp) with h1947 | h1947
                      · linarith only [h0, h1947, hlam]
                      · linarith only [h1335, h1947, hlam]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      rcases p1876_3 (m.d 0 2) (by simp) with h1950 | h1950
                      · linarith only [h0, h1950, hlam]
                      · linarith only [h1336, h1950, hlam]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      rcases p1876_3 (m.d 0 2) (by simp) with h1953 | h1953
                      · linarith only [h0, h1953, hlam]
                      · linarith only [h1337, h1953, hlam]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h1335, hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h1865, hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h1335, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1876_1, u2ehi3]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h0, h1335, h1872, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1876_1, u2ehi3]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h1336, hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h1866, hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h1870, hlam, p1876_1]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h1872, hlam, p1876_1]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h1337, hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h1867, hlam, p1876_0]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [h1871, hlam, p1876_1]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [hc25, hlam, hphi, p1876_1, u2ehi3]
                    · have p1876_0 := h1876c.1
                      have p1876_1 := h1876c.2.1
                      have p1876_2 := h1876c.2.2.1
                      have p1876_3 := h1876c.2.2.2
                      linarith only [hlam, p1876_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1971 | h1971
                · linarith only [h0, h1336, h1339, h1971, h664, hc01, hc12, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1973 | h1973
                  · linarith only [h1336, h1339, h1973, hc34, hlam, hphi, ht23, u2ehi3]
                  · rcases h2bigk with h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c | h1975c
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h0, hlam, p1975_1]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      rcases p1975_3 (m.d 0 2) (by simp) with h1978 | h1978
                      · rcases p1975_3 (m.d 1 2) (by simp) with h1979 | h1979
                        · rcases p1975_3 (m.d 2 3) (by simp) with h1980 | h1980
                          · linarith only [h1980, hlam, p1975_0]
                          · rcases p1975_3 (m.d 2 4) (by simp) with h1982 | h1982
                            · linarith only [h1336, h1982, hlam]
                            · rcases p1975_3 (m.d 2 5) (by simp) with h1984 | h1984
                              · linarith only [h1337, h1984, hlam]
                              · linarith only [h1871, h1984, hlam]
                        · linarith only [h1865, h1979, hlam]
                      · linarith only [h1978, hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      rcases p1975_3 (m.d 0 2) (by simp) with h1989 | h1989
                      · rcases p1975_3 (m.d 1 2) (by simp) with h1990 | h1990
                        · rcases p1975_3 (m.d 2 3) (by simp) with h1991 | h1991
                          · linarith only [h1335, h1991, hlam]
                          · linarith only [h1870, h1991, hlam]
                        · linarith only [h1866, h1990, hlam]
                      · linarith only [h1989, hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      rcases p1975_3 (m.d 0 2) (by simp) with h1996 | h1996
                      · rcases p1975_3 (m.d 1 2) (by simp) with h1997 | h1997
                        · rcases p1975_3 (m.d 2 3) (by simp) with h1998 | h1998
                          · linarith only [h1335, h1998, hlam]
                          · rcases p1975_3 (m.d 2 4) (by simp) with h2000 | h2000
                            · linarith only [h1336, h2000, hlam]
                            · rcases p1975_3 (m.d 2 5) (by simp) with h2002 | h2002
                              · linarith only [h2002, hlam, p1975_0]
                              · rcases h4bigk with h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [hlam, p2004_0]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h664, hlam, p2004_0]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1339, hc45, hlam, hphi, ht23, ht34, p2004_1, u2ehi3]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1339, hc34, hc45, hlam, hphi, p2004_1]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1339, hlam, p2004_0]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  rcases p2004_3 (m.d 0 4) (by simp) with h2010 | h2010
                                  · linarith only [h2010, h664, hlam]
                                  · rcases p2004_3 (m.d 1 4) (by simp) with h2012 | h2012
                                    · rcases p2004_3 (m.d 2 4) (by simp) with h2013 | h2013
                                      · linarith only [h1866, h2013, hlam]
                                      · rcases p2004_3 (m.d 3 4) (by simp) with h2015 | h2015
                                        · linarith only [h1868, h2015, hlam]
                                        · rcases p2004_3 (m.d 4 5) (by simp) with h2017 | h2017
                                          · linarith only [h1869, h2017, hlam]
                                          · linarith only [h1339, h2017, hlam]
                                    · linarith only [h2012, h664, hlam]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [hlam, p2004_0]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  rcases p2004_3 (m.d 0 4) (by simp) with h2022 | h2022
                                  · linarith only [h2022, h664, hlam]
                                  · linarith only [h1336, h2022, hlam]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1869, h1870, h1871, h1973, hlam, p2004_2]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1339, h664, hc01, hc14, hlam, hphi, p2004_1]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1336, hlam, p2004_1]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1866, hlam, p2004_1]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [hlam, p2004_0]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1336, h1339, hc34, hc45, hlam, hphi, p2004_1]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1971, hlam, p2004_0]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1338, hlam, p2004_1]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1868, hlam, p2004_0]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1870, hlam, p2004_0]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [hlam, p2004_0]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1973, hlam, p2004_0]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1336, hc45, hlam, hphi, ht23, ht34, p2004_1, u2ehi3]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1869, hlam, p2004_0]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [h1865, h1868, h1869, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2004_1, u2ehi3]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  rcases p2004_3 (m.d 0 4) (by simp) with h2040 | h2040
                                  · linarith only [h1339, h2040, hlam]
                                  · linarith only [h1338, h2040, hlam]
                                · have p2004_0 := h2004c.1
                                  have p2004_1 := h2004c.2.1
                                  have p2004_2 := h2004c.2.2.1
                                  have p2004_3 := h2004c.2.2.2
                                  linarith only [hlam, p2004_0]
                        · linarith only [h1867, h1997, hlam]
                      · linarith only [h1996, hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1335, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1975_1, u2ehi2]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      rcases p1975_3 (m.d 0 2) (by simp) with h2048 | h2048
                      · linarith only [h0, h2048, hlam]
                      · linarith only [h1335, h2048, hlam]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      rcases p1975_3 (m.d 0 2) (by simp) with h2051 | h2051
                      · linarith only [h0, h2051, hlam]
                      · linarith only [h1336, h2051, hlam]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      rcases p1975_3 (m.d 0 2) (by simp) with h2054 | h2054
                      · linarith only [h0, h2054, hlam]
                      · linarith only [h1337, h2054, hlam]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1335, hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1865, hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1337, h1871, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1975_1, u2ehi3]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1871, hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1336, hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1866, hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1870, hlam, p1975_1]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1971, hlam, p1975_1]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1337, hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1867, hlam, p1975_0]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1337, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1975_1, u2ehi2]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [h1337, h1339, h1865, h1868, h1869, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1975_1, u2ehi3]
                    · have p1975_0 := h1975c.1
                      have p1975_1 := h1975c.2.1
                      have p1975_2 := h1975c.2.2.1
                      have p1975_3 := h1975c.2.2.2
                      linarith only [hlam, p1975_0]
            · linarith only [h1338, h1339, h1865, h1868, h1869, h1870, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2073 | h2073
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2074 | h2074
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2075 | h2075
                · linarith only [h0, h1335, h1339, h2073, h2075, h664, hc01, hc12, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2077 | h2077
                  · linarith only [h1336, h1869, h2073, h2077, h664, hlam]
                  · rcases h2bigk with h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h0, hlam, p2079_1]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      rcases p2079_3 (m.d 0 2) (by simp) with h2082 | h2082
                      · rcases p2079_3 (m.d 1 2) (by simp) with h2083 | h2083
                        · rcases p2079_3 (m.d 2 3) (by simp) with h2084 | h2084
                          · linarith only [h2084, hlam, p2079_0]
                          · rcases p2079_3 (m.d 2 4) (by simp) with h2086 | h2086
                            · linarith only [h1336, h2086, hlam]
                            · rcases p2079_3 (m.d 2 5) (by simp) with h2088 | h2088
                              · linarith only [h1337, h2088, hlam]
                              · rcases h4bigk with h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c | h2090c
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [hlam, p2090_0]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h664, hlam, p2090_0]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1869, h664, hc45, hlam, hphi, ht23, ht34, p2090_1, u2ehi3]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1869, h664, hc34, hc45, hlam, hphi, p2090_1]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1339, hlam, p2090_0]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1869, hc04, hc45, hlam, hphi, p2090_1]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [hlam, p2090_0]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1869, hc45, hlam, hphi, ht23, ht34, p2090_1, u2ehi3]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1869, hc34, hc45, hlam, hphi, p2090_1]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1869, hlam, p2090_0]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1336, hlam, p2090_1]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1866, hlam, p2090_1]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [hlam, p2090_0]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h0, h2074, h2075, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2079_1, p2090_1]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h2075, hlam, p2090_0]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1338, hlam, p2090_1]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1868, hlam, p2090_0]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h2073, hlam, p2090_0]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [hlam, p2090_0]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h2077, hlam, p2090_0]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h1336, hc45, hlam, hphi, ht23, ht34, p2090_1, u2ehi3]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [h0, h2074, h2075, h664, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p2079_1, p2090_1, u2ehi3]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht23, ht34, p2090_1, u2ehi3]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  rcases p2090_3 (m.d 0 4) (by simp) with h2114 | h2114
                                  · linarith only [h1339, h2114, hlam]
                                  · linarith only [h1338, h2114, hlam]
                                · have p2090_0 := h2090c.1
                                  have p2090_1 := h2090c.2.1
                                  have p2090_2 := h2090c.2.2.1
                                  have p2090_3 := h2090c.2.2.2
                                  linarith only [hlam, p2090_0]
                        · linarith only [h1865, h2083, hlam]
                      · linarith only [h2082, hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      rcases p2079_3 (m.d 0 2) (by simp) with h2120 | h2120
                      · rcases p2079_3 (m.d 1 2) (by simp) with h2121 | h2121
                        · rcases p2079_3 (m.d 2 3) (by simp) with h2122 | h2122
                          · linarith only [h1335, h2122, hlam]
                          · linarith only [h2073, h2122, hlam]
                        · linarith only [h1866, h2121, hlam]
                      · linarith only [h2120, hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      rcases p2079_3 (m.d 0 2) (by simp) with h2127 | h2127
                      · rcases p2079_3 (m.d 1 2) (by simp) with h2128 | h2128
                        · rcases p2079_3 (m.d 2 3) (by simp) with h2129 | h2129
                          · linarith only [h1335, h2129, hlam]
                          · linarith only [h2074, h2129, hlam]
                        · linarith only [h1867, h2128, hlam]
                      · linarith only [h2127, hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h1335, h2074, h2075, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2079_1, u2ehi3]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      rcases p2079_3 (m.d 0 2) (by simp) with h2136 | h2136
                      · linarith only [h0, h2136, hlam]
                      · linarith only [h1335, h2136, hlam]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      rcases p2079_3 (m.d 0 2) (by simp) with h2139 | h2139
                      · linarith only [h0, h2139, hlam]
                      · linarith only [h1336, h2139, hlam]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      rcases p2079_3 (m.d 0 2) (by simp) with h2142 | h2142
                      · linarith only [h0, h2142, hlam]
                      · linarith only [h1337, h2142, hlam]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h1335, hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h1865, hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h1335, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2079_1, u2ehi3]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h0, h1335, h2075, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2079_1, u2ehi3]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h1336, hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h1866, hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h2073, hlam, p2079_1]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h2075, hlam, p2079_1]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h1337, hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h1867, hlam, p2079_0]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [h2074, hlam, p2079_1]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [hc25, hlam, hphi, p2079_1, u2ehi3]
                    · have p2079_0 := h2079c.1
                      have p2079_1 := h2079c.2.1
                      have p2079_2 := h2079c.2.2.1
                      have p2079_3 := h2079c.2.2.2
                      linarith only [hlam, p2079_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2160 | h2160
                · linarith only [h1336, h1339, h2160, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2162 | h2162
                  · linarith only [h1338, h1339, h2162, hlam]
                  · rcases h2bigk with h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h0, hlam, p2164_1]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      rcases p2164_3 (m.d 0 2) (by simp) with h2167 | h2167
                      · rcases p2164_3 (m.d 1 2) (by simp) with h2168 | h2168
                        · rcases p2164_3 (m.d 2 3) (by simp) with h2169 | h2169
                          · linarith only [h2169, hlam, p2164_0]
                          · rcases p2164_3 (m.d 2 4) (by simp) with h2171 | h2171
                            · linarith only [h1336, h2171, hlam]
                            · rcases p2164_3 (m.d 2 5) (by simp) with h2173 | h2173
                              · linarith only [h1337, h2173, hlam]
                              · linarith only [h2074, h2173, hlam]
                        · linarith only [h1865, h2168, hlam]
                      · linarith only [h2167, hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      rcases p2164_3 (m.d 0 2) (by simp) with h2178 | h2178
                      · rcases p2164_3 (m.d 1 2) (by simp) with h2179 | h2179
                        · rcases p2164_3 (m.d 2 3) (by simp) with h2180 | h2180
                          · linarith only [h1335, h2180, hlam]
                          · linarith only [h2073, h2180, hlam]
                        · linarith only [h1866, h2179, hlam]
                      · linarith only [h2178, hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      rcases p2164_3 (m.d 0 2) (by simp) with h2185 | h2185
                      · rcases p2164_3 (m.d 1 2) (by simp) with h2186 | h2186
                        · rcases p2164_3 (m.d 2 3) (by simp) with h2187 | h2187
                          · linarith only [h1335, h2187, hlam]
                          · rcases p2164_3 (m.d 2 4) (by simp) with h2189 | h2189
                            · linarith only [h1336, h2189, hlam]
                            · rcases p2164_3 (m.d 2 5) (by simp) with h2191 | h2191
                              · linarith only [h2191, hlam, p2164_0]
                              · rcases h4bigk with h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [hlam, p2193_0]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h664, hlam, p2193_0]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1869, h664, hc45, hlam, hphi, ht23, ht34, p2193_1, u2ehi3]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1869, h664, hc34, hc45, hlam, hphi, p2193_1]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1339, hlam, p2193_0]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1869, hc04, hc45, hlam, hphi, p2193_1]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [hlam, p2193_0]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1869, hc45, hlam, hphi, ht23, ht34, p2193_1, u2ehi3]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1869, hc34, hc45, hlam, hphi, p2193_1]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1869, hlam, p2193_0]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1336, hlam, p2193_1]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1866, hlam, p2193_1]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [hlam, p2193_0]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1336, h1869, h664, hc34, hc45, hlam, hphi, p2193_1]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h2160, hlam, p2193_0]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1338, hlam, p2193_1]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1868, hlam, p2193_0]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h2073, hlam, p2193_0]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [hlam, p2193_0]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h2162, hlam, p2193_0]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h1336, hc45, hlam, hphi, ht23, ht34, p2193_1, u2ehi3]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [h664, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2193_1]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht23, ht34, p2193_1, u2ehi3]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  rcases p2193_3 (m.d 0 4) (by simp) with h2217 | h2217
                                  · linarith only [h1339, h2217, hlam]
                                  · linarith only [h1338, h2217, hlam]
                                · have p2193_0 := h2193c.1
                                  have p2193_1 := h2193c.2.1
                                  have p2193_2 := h2193c.2.2.1
                                  have p2193_3 := h2193c.2.2.2
                                  linarith only [hlam, p2193_0]
                        · linarith only [h1867, h2186, hlam]
                      · linarith only [h2185, hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h1335, h2073, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2164_1, u2ehi3]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      rcases p2164_3 (m.d 0 2) (by simp) with h2225 | h2225
                      · linarith only [h0, h2225, hlam]
                      · linarith only [h1335, h2225, hlam]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      rcases p2164_3 (m.d 0 2) (by simp) with h2228 | h2228
                      · linarith only [h0, h2228, hlam]
                      · linarith only [h1336, h2228, hlam]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      rcases p2164_3 (m.d 0 2) (by simp) with h2231 | h2231
                      · linarith only [h0, h2231, hlam]
                      · linarith only [h1337, h2231, hlam]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h1335, hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h1865, hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h1337, h2074, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2164_1, u2ehi3]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h2074, hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h1336, hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h1866, hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h2073, hlam, p2164_1]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h2160, hlam, p2164_1]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h1337, hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h1867, hlam, p2164_0]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h1337, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2164_1, u2ehi2]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [h0, h1337, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2164_1, u2ehi3]
                    · have p2164_0 := h2164c.1
                      have p2164_1 := h2164c.2.1
                      have p2164_2 := h2164c.2.2.1
                      have p2164_3 := h2164c.2.2.2
                      linarith only [hlam, p2164_0]
            · linarith only [h1338, h1339, h2073, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · linarith only [h1338, h1339, h1865, h1868, hc45, hlam, hphi, ht23, ht34, u2ehi2]
      · linarith only [h0, h1337, h1867, hlam]
    · linarith only [h0, h1337, h1866, hc24, hlam, hphi, u2ehi4]
  · linarith only [h0, h1337, h1865, hc23, hlam, hphi, u2ehi4]

set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1337 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1338 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h1339 | h1339
  · exact r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x0_x0_x0 m hb2 hb4 h0 h664 h1335 h1336 h1337 h1338 h1339
  · exact r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x0_x0_x1 m hb2 hb4 h0 h664 h1335 h1336 h1337 h1338 h1339

end R2N4
