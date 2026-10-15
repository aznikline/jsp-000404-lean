import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_49S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1899 | h1899
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1900 | h1900
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1901 | h1901
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1902 | h1902
        · linarith only [h0, h1902, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1904 | h1904
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1905 | h1905
            · linarith only [h1901, h1902, h1905, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1907 | h1907
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1908 | h1908
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1909 | h1909
                  · linarith only [h0, h1901, h1905, h1907, h1909, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                  · linarith only [h1899, h1909, h4, hlam]
                · linarith only [h1900, h1908, h4, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1913 | h1913
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1914 | h1914
                  · linarith only [h0, h1901, h1905, h1914, h4, hc24, hlam, hphi, ht12, u1ehi3]
                  · linarith only [h1899, h1914, h4, hlam]
                · linarith only [h1900, h1902, h1913, h4, hc24, hlam, hphi, ht12, u1ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1918 | h1918
            · linarith only [h1901, h1902, h1918, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1920 | h1920
              · linarith only [h1901, h1904, h1920, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1922 | h1922
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1923 | h1923
                  · linarith only [h0, h1901, h1918, h1923, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                  · linarith only [h1899, h1923, h4, hlam]
                · linarith only [h1900, h1922, h4, hc24, hlam, hphi, ht12, u1ehi3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1927 | h1927
        · linarith only [h0, h1927, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1929 | h1929
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1930 | h1930
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1931 | h1931
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1932 | h1932
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1933 | h1933
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1934 | h1934
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1935 | h1935
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1936 | h1936
                        · rcases h1bigk with h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            rcases p1937_3 (m.d 0 1) (by simp) with h1939 | h1939
                            · rcases p1937_3 (m.d 1 2) (by simp) with h1940 | h1940
                              · linarith only [h1940, hlam, p1937_0]
                              · rcases p1937_3 (m.d 1 3) (by simp) with h1942 | h1942
                                · linarith only [h1, h1942, hlam]
                                · linarith only [h1901, h1942, hlam]
                            · linarith only [h1939, hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1930, h1936, hc01, hc45, hlam, hphi, ht0b, ht5b, p1937_1]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            rcases p1937_3 (m.d 0 1) (by simp) with h1947 | h1947
                            · rcases p1937_3 (m.d 1 2) (by simp) with h1948 | h1948
                              · linarith only [h0, h1948, hlam]
                              · rcases p1937_3 (m.d 1 3) (by simp) with h1950 | h1950
                                · linarith only [h1, h1950, hlam]
                                · linarith only [h1930, h1950, hlam]
                            · linarith only [h1947, hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            rcases p1937_3 (m.d 0 1) (by simp) with h1954 | h1954
                            · rcases p1937_3 (m.d 1 2) (by simp) with h1955 | h1955
                              · linarith only [h0, h1955, hlam]
                              · linarith only [h1929, h1955, hlam]
                            · linarith only [h1954, hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h0, hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1901, hlam, p1937_1]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1927, hlam, p1937_1]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [hc12, hlam, hphi, p1937_1, u1ehi4]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1, hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [hc13, hlam, hphi, p1937_1, u1ehi1]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1937_1, u1ehi3]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1937_1, u1ehi4]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h2, hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1929, hc14, hlam, hphi, p1937_1, u1ehi4]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1930, hlam, p1937_1]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1, h1930, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1937_1, u1ehi4]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h3, hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1929, hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1931, hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [h1932, hlam, p1937_0]
                          · have p1937_0 := h1937c.1
                            have p1937_1 := h1937c.2.1
                            have p1937_2 := h1937c.2.2.1
                            have p1937_3 := h1937c.2.2.2
                            linarith only [hlam, p1937_0]
                        · rcases h1bigk with h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1929, h1935, h1936, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1979_1]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1901, h1929, h1935, h1936, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1979_1]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1927, h1929, h1935, h1936, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1979_1]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            rcases p1979_3 (m.d 0 1) (by simp) with h1984 | h1984
                            · rcases p1979_3 (m.d 1 2) (by simp) with h1985 | h1985
                              · linarith only [h0, h1985, hlam]
                              · linarith only [h1929, h1985, hlam]
                            · linarith only [h1984, hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h0, hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1901, hlam, p1979_1]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1927, hlam, p1979_1]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h0, h1933, h4, hc23, hlam, hphi, ht12, p1979_1, u1ehi4]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1, hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1929, h1935, h1936, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1979_1]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1, h1927, h1929, h1935, h1936, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1979_1]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h0, h1, h1929, h1933, h1935, h1936, h4, hc01, hc23, hc34, hlam, hphi, ht0b, ht12, ht45, ht5b, p1979_1, u1ehi4]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h2, hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1929, h1935, h1936, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1979_1]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1930, hlam, p1979_1]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h0, h1, h1929, h1930, h1933, h1935, h1936, h4, hc01, hc23, hc34, hlam, hphi, ht0b, ht12, ht45, ht5b, p1979_1, u1ehi4]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h3, hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1929, hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1931, hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [h1932, hlam, p1979_0]
                          · have p1979_0 := h1979c.1
                            have p1979_1 := h1979c.2.1
                            have p1979_2 := h1979c.2.2.1
                            have p1979_3 := h1979c.2.2.2
                            linarith only [hlam, p1979_0]
                      · linarith only [h0, h1935, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h1901, h1929, h1934, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                  · linarith only [h1901, h1929, h1933, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                · linarith only [h1900, h1932, h4, hc24, hlam, hphi, ht12, u1ehi3]
              · linarith only [h1901, h1929, h1931, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2014 | h2014
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2015 | h2015
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2016 | h2016
                  · linarith only [h1901, h1930, h2016, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h1901, h1929, h2016, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                · linarith only [h1900, h2015, h4, hc24, hlam, hphi, ht12, u1ehi3]
              · linarith only [h1901, h1929, h2014, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2021 | h2021
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2022 | h2022
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2023 | h2023
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2024 | h2024
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2025 | h2025
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2026 | h2026
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2027 | h2027
                        · rcases h1bigk with h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            rcases p2028_3 (m.d 0 1) (by simp) with h2030 | h2030
                            · rcases p2028_3 (m.d 1 2) (by simp) with h2031 | h2031
                              · linarith only [h2031, hlam, p2028_0]
                              · rcases p2028_3 (m.d 1 3) (by simp) with h2033 | h2033
                                · linarith only [h1, h2033, hlam]
                                · linarith only [h1901, h2033, hlam]
                            · linarith only [h2030, hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h2021, h2027, hc01, hc45, hlam, hphi, ht0b, ht5b, p2028_1]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            rcases p2028_3 (m.d 0 1) (by simp) with h2038 | h2038
                            · rcases p2028_3 (m.d 1 2) (by simp) with h2039 | h2039
                              · linarith only [h0, h2039, hlam]
                              · rcases p2028_3 (m.d 1 3) (by simp) with h2041 | h2041
                                · linarith only [h1, h2041, hlam]
                                · linarith only [h2021, h2041, hlam]
                            · linarith only [h2038, hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            rcases p2028_3 (m.d 0 1) (by simp) with h2045 | h2045
                            · rcases p2028_3 (m.d 1 2) (by simp) with h2046 | h2046
                              · linarith only [h0, h2046, hlam]
                              · rcases p2028_3 (m.d 1 3) (by simp) with h2048 | h2048
                                · linarith only [h1, h2048, hlam]
                                · linarith only [h2022, h2048, hlam]
                            · linarith only [h2045, hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h0, hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h1901, hlam, p2028_1]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h1927, hlam, p2028_1]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h1929, hlam, p2028_1]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h1, hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [hc13, hlam, hphi, p2028_1, u1ehi1]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h1, h1929, h2023, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2028_1, u1ehi1]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h1, h1929, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2028_1, u1ehi1]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h2, hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [hc14, hlam, hphi, p2028_1, u1ehi1]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h2021, hlam, p2028_1]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h1, h1929, h2021, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2028_1, u1ehi1]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h3, hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [hc15, hlam, hphi, p2028_1, u1ehi1]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h2022, hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [h2023, hlam, p2028_0]
                          · have p2028_0 := h2028c.1
                            have p2028_1 := h2028c.2.1
                            have p2028_2 := h2028c.2.2.1
                            have p2028_3 := h2028c.2.2.2
                            linarith only [hlam, p2028_0]
                        · rcases h1bigk with h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            rcases p2072_3 (m.d 0 1) (by simp) with h2074 | h2074
                            · rcases p2072_3 (m.d 1 2) (by simp) with h2075 | h2075
                              · linarith only [h2075, hlam, p2072_0]
                              · rcases p2072_3 (m.d 1 3) (by simp) with h2077 | h2077
                                · linarith only [h1, h2077, hlam]
                                · linarith only [h1901, h2077, hlam]
                            · linarith only [h2074, hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h2021, h2023, h2027, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2072_1]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h2023, h2027, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2072_1]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            rcases p2072_3 (m.d 0 1) (by simp) with h2083 | h2083
                            · rcases p2072_3 (m.d 1 2) (by simp) with h2084 | h2084
                              · linarith only [h0, h2084, hlam]
                              · rcases p2072_3 (m.d 1 3) (by simp) with h2086 | h2086
                                · linarith only [h1, h2086, hlam]
                                · linarith only [h2022, h2086, hlam]
                            · linarith only [h2083, hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h0, hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h1901, hlam, p2072_1]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h1927, hlam, p2072_1]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h1929, hlam, p2072_1]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h1, hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [hc13, hlam, hphi, p2072_1, u1ehi1]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h1, h2023, h2027, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2072_1]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2072_1, u1ehi4]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h2, hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [hc14, hlam, hphi, p2072_1, u1ehi1]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h2021, hlam, p2072_1]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h1, h1929, h2021, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2072_1, u1ehi1]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h3, hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [hc15, hlam, hphi, p2072_1, u1ehi1]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h2022, hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [h2023, hlam, p2072_0]
                          · have p2072_0 := h2072c.1
                            have p2072_1 := h2072c.2.1
                            have p2072_2 := h2072c.2.2.1
                            have p2072_3 := h2072c.2.2.2
                            linarith only [hlam, p2072_0]
                      · linarith only [h0, h2026, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h1901, h2025, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h1, h1899, h1901, h2024, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                · linarith only [h1900, h2023, h4, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2114 | h2114
                · linarith only [h2021, h2022, h2114, hlam]
                · linarith only [h1900, h1927, h2114, h4, hc24, hlam, hphi, ht12, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2117 | h2117
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2118 | h2118
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2119 | h2119
                  · linarith only [h2021, h2119, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h1901, h2119, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h1900, h1929, h2021, h2117, h2118, h4, hc24, hlam, hphi, ht12, u1ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2123 | h2123
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2124 | h2124
                  · linarith only [h2021, h2124, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h1901, h2124, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h1900, h2123, h4, hc24, hlam, hphi, ht12, u1ehi3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2128 | h2128
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2129 | h2129
        · linarith only [h0, h2129, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2131 | h2131
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2132 | h2132
            · linarith only [h2128, h2129, h2132, hlam]
            · linarith only [h1899, h1900, h2132, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2135 | h2135
            · linarith only [h2128, h2129, h2135, hlam]
            · linarith only [h1899, h1900, h2135, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2138 | h2138
        · linarith only [h0, h2138, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2140 | h2140
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2141 | h2141
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2142 | h2142
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2143 | h2143
                · linarith only [h1900, h2, h2143, hlam]
                · linarith only [h2138, h2140, h2143, hlam]
              · linarith only [h2138, h2140, h2141, h2142, hlam]
            · linarith only [h1899, h1900, h2141, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2148 | h2148
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2149 | h2149
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2150 | h2150
                · linarith only [h1900, h2, h2150, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2152 | h2152
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2153 | h2153
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2154 | h2154
                      · linarith only [h1900, h2, h2138, h2152, h2154, hc23, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h0, h2154, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h2128, h2149, h2153, hc13, hlam, hphi, u1ehi1]
                  · linarith only [h2128, h2148, h2152, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2159 | h2159
                · linarith only [h1900, h2, h2159, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2161 | h2161
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2162 | h2162
                    · linarith only [h2149, h2162, hc23, hlam, hphi, ht12, u1ehi2]
                    · linarith only [h2128, h2162, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h2128, h2148, h2161, hc13, hlam, hphi, u1ehi1]
            · linarith only [h1899, h1900, h2148, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2167 | h2167
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2168 | h2168
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2169 | h2169
        · linarith only [h0, h2169, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2171 | h2171
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2172 | h2172
            · linarith only [h1, h1899, h2172, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2174 | h2174
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2175 | h2175
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2176 | h2176
                  · linarith only [h0, h1, h1899, h2168, h2174, h2176, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2178 | h2178
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2179 | h2179
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2180 | h2180
                        · rcases h1bigk with h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h2168, h2178, h2180, hc01, hc45, hlam, hphi, ht0b, ht5b, p2181_1]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            rcases p2181_3 (m.d 0 1) (by simp) with h2184 | h2184
                            · rcases p2181_3 (m.d 1 2) (by simp) with h2185 | h2185
                              · linarith only [h0, h2185, hlam]
                              · linarith only [h2168, h2185, hlam]
                            · linarith only [h2184, hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h2168, h2169, h2178, h2180, hc01, hc45, hlam, hphi, ht0b, ht5b, p2181_1]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            rcases p2181_3 (m.d 0 1) (by simp) with h2190 | h2190
                            · rcases p2181_3 (m.d 1 2) (by simp) with h2191 | h2191
                              · linarith only [h0, h2191, hlam]
                              · linarith only [h2171, h2191, hlam]
                            · linarith only [h2190, hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h0, hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h0, h2174, h2176, h4, hc34, hlam, hphi, ht12, ht23, p2181_1, u1ehi4]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h2169, hlam, p2181_1]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h0, h2176, h4, hc34, hlam, hphi, ht12, ht23, p2181_1, u1ehi4]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h1, hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h2168, hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h2172, hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [hc13, hlam, hphi, p2181_1, u1ehi4]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h2, hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h2168, h2178, h2180, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2181_1]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h0, h2, h2168, h2176, h2178, h2180, h4, hc01, hc34, hc45, hlam, hphi, ht0b, ht12, ht23, ht5b, p2181_1, u1ehi2]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h0, h2, h2168, h2176, h2178, h2180, h4, hc01, hc34, hc45, hlam, hphi, ht0b, ht12, ht23, ht5b, p2181_1, u1ehi4]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h3, hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h2171, hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h2174, hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [h2175, hlam, p2181_0]
                          · have p2181_0 := h2181c.1
                            have p2181_1 := h2181c.2.1
                            have p2181_2 := h2181c.2.2.1
                            have p2181_3 := h2181c.2.2.2
                            linarith only [hlam, p2181_0]
                        · linarith only [h0, h2168, h2176, h2178, h2180, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h0, h2168, h2174, h2175, h2179, h4, hlam]
                    · linarith only [h0, h2168, h2174, h2176, h2178, h4, hc23, hc34, hlam, hphi]
                · linarith only [h1899, h2167, h2175, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2219 | h2219
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2220 | h2220
                  · linarith only [h1, h1899, h2220, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2222 | h2222
                    · linarith only [h2, h2168, h2169, h2174, h2222, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2224 | h2224
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2225 | h2225
                        · rcases h1bigk with h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c | h2226c
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            rcases p2226_3 (m.d 0 1) (by simp) with h2228 | h2228
                            · rcases p2226_3 (m.d 1 2) (by simp) with h2229 | h2229
                              · linarith only [h2229, hlam, p2226_0]
                              · rcases p2226_3 (m.d 1 3) (by simp) with h2231 | h2231
                                · linarith only [h1, h2231, hlam]
                                · rcases p2226_3 (m.d 1 4) (by simp) with h2233 | h2233
                                  · linarith only [h2, h2233, hlam]
                                  · linarith only [h2169, h2233, hlam]
                            · linarith only [h2228, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            rcases p2226_3 (m.d 0 1) (by simp) with h2237 | h2237
                            · rcases p2226_3 (m.d 1 2) (by simp) with h2238 | h2238
                              · linarith only [h0, h2238, hlam]
                              · linarith only [h2168, h2238, hlam]
                            · linarith only [h2237, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            rcases p2226_3 (m.d 0 1) (by simp) with h2242 | h2242
                            · rcases p2226_3 (m.d 1 2) (by simp) with h2243 | h2243
                              · linarith only [h0, h2243, hlam]
                              · rcases p2226_3 (m.d 1 3) (by simp) with h2245 | h2245
                                · linarith only [h1, h2245, hlam]
                                · rcases p2226_3 (m.d 1 4) (by simp) with h2247 | h2247
                                  · linarith only [h2247, hlam, p2226_0]
                                  · rcases p2226_3 (m.d 1 5) (by simp) with h2249 | h2249
                                    · linarith only [h2249, h3, hlam]
                                    · rcases h4bigk with h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [hlam, p2251_0]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2169, h2171, h2220, h2222, h4, hc23, hc34, hlam, hphi, p2251_1]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h4, hlam, p2251_1]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h1899, hlam, p2251_1]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        rcases p2251_3 (m.d 0 4) (by simp) with h2256 | h2256
                                        · rcases p2251_3 (m.d 1 4) (by simp) with h2257 | h2257
                                          · linarith only [h2, h2257, hlam]
                                          · linarith only [h2219, h2257, hlam]
                                        · linarith only [h2256, hlam, p2251_0]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2, hlam, p2251_0]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [hlam, p2251_0]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2169, hlam, p2251_1]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2172, hlam, p2251_1]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p2226_1, p2251_1]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2, h2169, h2171, h2174, h2220, hc34, hlam, hphi, ht12, ht23, p2251_1, u1ehi2]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2169, h2171, h2174, h2220, hc34, hlam, hphi, ht12, ht23, p2251_1, u1ehi2]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [hlam, p2251_0]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2220, hlam, p2251_1]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        rcases p2251_3 (m.d 0 4) (by simp) with h2270 | h2270
                                        · linarith only [h2270, h4, hlam]
                                        · linarith only [h2167, h2270, hlam]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2, h2169, h2171, h2174, hc34, hlam, hphi, ht12, ht23, p2251_1, u1ehi2]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2169, h2171, h2174, hc34, hlam, hphi, ht12, ht23, p2251_1, u1ehi2]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h0, h2171, h2174, h4, hc34, hlam, hphi, ht12, ht23, p2251_1, u1ehi2]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [hlam, p2251_0]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        rcases p2251_3 (m.d 0 4) (by simp) with h2277 | h2277
                                        · linarith only [h1899, h2277, hlam]
                                        · linarith only [h2167, h2277, hlam]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2167, hlam, p2251_0]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2219, hlam, p2251_0]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2224, hlam, p2251_0]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [h2225, hlam, p2251_0]
                                      · have p2251_0 := h2251c.1
                                        have p2251_1 := h2251c.2.1
                                        have p2251_2 := h2251c.2.2.1
                                        have p2251_3 := h2251c.2.2.2
                                        linarith only [hlam, p2251_0]
                            · linarith only [h2242, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            rcases p2226_3 (m.d 0 1) (by simp) with h2286 | h2286
                            · rcases p2226_3 (m.d 1 2) (by simp) with h2287 | h2287
                              · linarith only [h0, h2287, hlam]
                              · linarith only [h2171, h2287, hlam]
                            · linarith only [h2286, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h0, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [hc12, hlam, hphi, p2226_1, u1ehi2]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h2169, hlam, p2226_1]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h0, h4, hc24, hlam, hphi, ht12, p2226_1, u1ehi4]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h1, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h2168, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h2172, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h2174, hlam, p2226_1]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h2, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2226_1, u1ehi1]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2226_1, u1ehi2]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h2, h2174, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2226_1, u1ehi2]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h3, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h2171, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h2171, hc12, hlam, hphi, p2226_1, u1ehi2]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [h2219, hlam, p2226_0]
                          · have p2226_0 := h2226c.1
                            have p2226_1 := h2226c.2.1
                            have p2226_2 := h2226c.2.2.1
                            have p2226_3 := h2226c.2.2.2
                            linarith only [hlam, p2226_0]
                        · linarith only [h0, h2220, h2225, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                      · linarith only [h2167, h2219, h2224, h3, h4, hlam]
                · linarith only [h2167, h2219, h4, hc24, hlam, hphi, ht12, u1ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2314 | h2314
            · linarith only [h1, h1899, h2314, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2316 | h2316
              · linarith only [h2168, h2171, h2316, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2318 | h2318
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2319 | h2319
                  · linarith only [h1, h1899, h2319, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2321 | h2321
                    · linarith only [h0, h2168, h2316, h2321, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2323 | h2323
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2324 | h2324
                        · rcases h1bigk with h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            rcases p2325_3 (m.d 0 1) (by simp) with h2327 | h2327
                            · rcases p2325_3 (m.d 1 2) (by simp) with h2328 | h2328
                              · linarith only [h2328, hlam, p2325_0]
                              · rcases p2325_3 (m.d 1 3) (by simp) with h2330 | h2330
                                · linarith only [h1, h2330, hlam]
                                · rcases p2325_3 (m.d 1 4) (by simp) with h2332 | h2332
                                  · linarith only [h2, h2332, hlam]
                                  · linarith only [h2169, h2332, hlam]
                            · linarith only [h2327, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            rcases p2325_3 (m.d 0 1) (by simp) with h2336 | h2336
                            · rcases p2325_3 (m.d 1 2) (by simp) with h2337 | h2337
                              · linarith only [h0, h2337, hlam]
                              · linarith only [h2168, h2337, hlam]
                            · linarith only [h2336, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            rcases p2325_3 (m.d 0 1) (by simp) with h2341 | h2341
                            · rcases p2325_3 (m.d 1 2) (by simp) with h2342 | h2342
                              · linarith only [h0, h2342, hlam]
                              · rcases p2325_3 (m.d 1 3) (by simp) with h2344 | h2344
                                · linarith only [h1, h2344, hlam]
                                · rcases p2325_3 (m.d 1 4) (by simp) with h2346 | h2346
                                  · linarith only [h2346, hlam, p2325_0]
                                  · rcases p2325_3 (m.d 1 5) (by simp) with h2348 | h2348
                                    · linarith only [h2348, h3, hlam]
                                    · rcases h4bigk with h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [hlam, p2350_0]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2168, h2171, h2318, h2319, h4, hc34, hlam, hphi, ht12, ht23, p2350_1, u1ehi2]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h4, hlam, p2350_1]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h1899, hlam, p2350_1]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        rcases p2350_3 (m.d 0 4) (by simp) with h2355 | h2355
                                        · rcases p2350_3 (m.d 1 4) (by simp) with h2356 | h2356
                                          · linarith only [h2, h2356, hlam]
                                          · linarith only [h2318, h2356, hlam]
                                        · linarith only [h2355, hlam, p2350_0]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2, hlam, p2350_0]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [hlam, p2350_0]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2169, hlam, p2350_1]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2314, hlam, p2350_1]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p2325_1, p2350_1]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2, h2168, h2171, h2318, h2319, hc34, hlam, hphi, ht12, ht23, p2350_1, u1ehi2]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2168, h2171, h2318, h2319, hc34, hlam, hphi, ht12, ht23, p2350_1, u1ehi2]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [hlam, p2350_0]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2319, hlam, p2350_1]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        rcases p2350_3 (m.d 0 4) (by simp) with h2369 | h2369
                                        · linarith only [h2369, h4, hlam]
                                        · linarith only [h2167, h2369, hlam]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2, h2168, h2171, h2318, hc34, hlam, hphi, ht12, ht23, p2350_1, u1ehi2]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2168, h2171, h2318, hc34, hlam, hphi, ht12, ht23, p2350_1, u1ehi2]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h0, h2168, h4, hc34, hlam, hphi, ht12, ht23, p2350_1, u1ehi2]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [hlam, p2350_0]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        rcases p2350_3 (m.d 0 4) (by simp) with h2376 | h2376
                                        · linarith only [h1899, h2376, hlam]
                                        · linarith only [h2167, h2376, hlam]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2167, hlam, p2350_0]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2318, hlam, p2350_0]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2323, hlam, p2350_0]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [h2324, hlam, p2350_0]
                                      · have p2350_0 := h2350c.1
                                        have p2350_1 := h2350c.2.1
                                        have p2350_2 := h2350c.2.2.1
                                        have p2350_3 := h2350c.2.2.2
                                        linarith only [hlam, p2350_0]
                            · linarith only [h2341, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            rcases p2325_3 (m.d 0 1) (by simp) with h2385 | h2385
                            · rcases p2325_3 (m.d 1 2) (by simp) with h2386 | h2386
                              · linarith only [h0, h2386, hlam]
                              · rcases p2325_3 (m.d 1 3) (by simp) with h2388 | h2388
                                · linarith only [h1, h2388, hlam]
                                · rcases p2325_3 (m.d 1 4) (by simp) with h2390 | h2390
                                  · linarith only [h2, h2390, hlam]
                                  · linarith only [h2318, h2390, hlam]
                            · linarith only [h2385, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h0, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [hc12, hlam, hphi, p2325_1, u1ehi2]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2169, hlam, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2171, hlam, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h1, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2168, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2314, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2316, hlam, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2, h2168, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2325_1]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2325_1, u1ehi2]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2325_1, u1ehi4]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h3, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2168, hc15, hlam, hphi, p2325_1, u1ehi2]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2325_1, u1ehi2]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [h2318, hlam, p2325_0]
                          · have p2325_0 := h2325c.1
                            have p2325_1 := h2325c.2.1
                            have p2325_2 := h2325c.2.2.1
                            have p2325_3 := h2325c.2.2.2
                            linarith only [hlam, p2325_0]
                        · linarith only [h0, h2168, h2319, h2324, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h2, h2167, h2318, h2323, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                · linarith only [h2167, h2318, h4, hc24, hlam, hphi, ht12, u1ehi3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2417 | h2417
        · linarith only [h0, h2417, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2419 | h2419
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2420 | h2420
            · linarith only [h1, h1899, h2420, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2422 | h2422
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2423 | h2423
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2424 | h2424
                  · linarith only [h1, h1899, h2168, h2424, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h2168, h2419, h2424, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                · linarith only [h1899, h2167, h2168, h2419, h2420, h2423, hc34, hlam, hphi, ht12, ht23, u1ehi4]
              · linarith only [h2168, h2419, h2422, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2429 | h2429
            · linarith only [h1, h1899, h2429, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2431 | h2431
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2432 | h2432
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2433 | h2433
                  · linarith only [h1, h1899, h2419, h2431, h2433, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h2168, h2433, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h1899, h2167, h2419, h2429, h2431, h2432, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2437 | h2437
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2438 | h2438
                  · linarith only [h1, h1899, h2438, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h2168, h2438, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h1899, h2167, h2437, hc34, hlam, hphi, ht12, ht23, u1ehi3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2442 | h2442
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2443 | h2443
        · linarith only [h0, h2443, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2445 | h2445
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2446 | h2446
            · linarith only [h1, h1899, h2446, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2448 | h2448
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2449 | h2449
                · linarith only [h2, h2167, h2449, hlam]
                · linarith only [h2442, h2443, h2448, h2449, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2452 | h2452
                · linarith only [h0, h2167, h2452, h4, hc14, hlam, hphi, u1ehi1]
                · linarith only [h2443, h2445, h2452, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2455 | h2455
            · linarith only [h1, h1899, h2455, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2457 | h2457
              · linarith only [h2442, h2445, h2457, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2459 | h2459
                · linarith only [h2, h2167, h2459, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2461 | h2461
                  · linarith only [h0, h1, h1899, h2442, h2461, h4, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2463 | h2463
                    · linarith only [h2, h2167, h2442, h2443, h2457, h2463, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2465 | h2465
                      · linarith only [h2, h2167, h2442, h2443, h2461, h2465, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2442, h2465, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2468 | h2468
        · linarith only [h0, h2468, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2470 | h2470
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2471 | h2471
            · linarith only [h1, h1899, h2471, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2473 | h2473
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2474 | h2474
                · linarith only [h1, h1899, h2167, h2442, h2470, h2474, hc14, hlam, hphi, u1ehi4]
                · linarith only [h2468, h2470, h2474, hlam]
              · linarith only [h2442, h2470, h2473, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2478 | h2478
            · linarith only [h1, h1899, h2478, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2480 | h2480
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2481 | h2481
                · linarith only [h2, h2167, h2481, hlam]
                · linarith only [h2478, h2480, h2481, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2484 | h2484
                · linarith only [h2, h2167, h2484, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2486 | h2486
                  · linarith only [h1, h1899, h2486, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h2442, h2486, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0 m hb1 hb4 h0 h1 h2 h3 h4
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x1 m hb1 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x0_x0 m hb1 hb4 h0 h1 h2 h3
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x0_x1 m hb1 hb4 h0 h1 h2 h3

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x0 m hb1 hb4 h0 h1 h2
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x1 m hb1 hb4 h0 h1 h2

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_21_14_M_IR_L_I_x0_x0 m hb1 hb4 h0 h1
  · exact r1l7_21_14_M_IR_L_I_x0_x1 m hb1 hb4 h0 h1

end R2N4
