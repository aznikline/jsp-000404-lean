import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5024000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1819 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1947 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1948 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1949 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  have h1819 := hg1819
  rcases m.htr 1 2 3 (by decide) (by decide) with h1950 | h1950
  · linarith only [h0, h1950, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1952 | h1952
    · linarith only [h0, h1304, h1949, h1952, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1954 | h1954
      · linarith only [h0, h1819, h1954, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1956 | h1956
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1957 | h1957
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1958 | h1958
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1959 | h1959
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1960 | h1960
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1961 | h1961
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1962 | h1962
                    · linarith only [h1, h1956, h1962, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h1958, h1962, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1, h1956, h1958, h1961, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h1, h1957, h1960, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h1947, h1959, h4, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1968 | h1968
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1969 | h1969
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1970 | h1970
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1971 | h1971
                    · linarith only [h1956, h1958, h1971, hlam]
                    · rcases h0bigk with h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        rcases p1973_3 (m.d 0 1) (by simp) with h1975 | h1975
                        · rcases p1973_3 (m.d 0 2) (by simp) with h1976 | h1976
                          · linarith only [h0, h1976, hlam]
                          · rcases p1973_3 (m.d 0 3) (by simp) with h1978 | h1978
                            · linarith only [h1, h1978, hlam]
                            · linarith only [h1978, h4, hlam]
                        · linarith only [h0, h1975, hlam]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1947, h1949, h1952, h1958, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u0elo0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1949, h1952, h1958, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u0elo0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1949, h1952, h1958, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u0elo0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h4, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1304, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1819, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        rcases p1973_3 (m.d 0 1) (by simp) with h1991 | h1991
                        · rcases p1973_3 (m.d 0 2) (by simp) with h1992 | h1992
                          · linarith only [h1992, h4, hlam]
                          · rcases p1973_3 (m.d 0 3) (by simp) with h1994 | h1994
                            · rcases p1973_3 (m.d 0 4) (by simp) with h1995 | h1995
                              · linarith only [h1947, h1995, hlam]
                              · linarith only [h1304, h1995, hlam]
                            · linarith only [h1994, h4, hlam]
                        · linarith only [h0, h1991, hlam]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1949, h1952, h1958, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u0elo2]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1, h1949, h1952, h1958, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u0elo0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h2, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        rcases p1973_3 (m.d 0 1) (by simp) with h2004 | h2004
                        · rcases p1973_3 (m.d 0 2) (by simp) with h2005 | h2005
                          · linarith only [h1304, h2005, hlam]
                          · rcases p1973_3 (m.d 0 3) (by simp) with h2007 | h2007
                            · rcases p1973_3 (m.d 0 4) (by simp) with h2008 | h2008
                              · rcases p1973_3 (m.d 0 5) (by simp) with h2009 | h2009
                                · linarith only [h1949, h2009, hlam]
                                · linarith only [h1819, h2009, hlam]
                              · linarith only [h1304, h2008, hlam]
                            · linarith only [h2007, h4, hlam]
                        · linarith only [h0, h2004, hlam]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1947, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1949, h1952, h1958, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u0elo3]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h3, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        rcases p1973_3 (m.d 0 1) (by simp) with h2019 | h2019
                        · rcases p1973_3 (m.d 0 2) (by simp) with h2020 | h2020
                          · linarith only [h1819, h2020, hlam]
                          · rcases p1973_3 (m.d 0 3) (by simp) with h2022 | h2022
                            · rcases p1973_3 (m.d 0 4) (by simp) with h2023 | h2023
                              · rcases p1973_3 (m.d 0 5) (by simp) with h2024 | h2024
                                · rcases h0emin with h2025 | h2025 | h2025 | h2025 | h2025
                                  · rcases h1bigk with h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      rcases p2026_3 (m.d 0 1) (by simp) with h2028 | h2028
                                      · rcases p2026_3 (m.d 1 2) (by simp) with h2029 | h2029
                                        · linarith only [h2029, hlam, p2026_0]
                                        · rcases p2026_3 (m.d 1 3) (by simp) with h2031 | h2031
                                          · linarith only [h1, h2031, hlam]
                                          · linarith only [h1950, h2031, hlam]
                                      · linarith only [h2028, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1957, hc35, hlam, hphi, ht0b, ht5b, p2026_1, u0elo0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      rcases p2026_3 (m.d 0 1) (by simp) with h2036 | h2036
                                      · rcases p2026_3 (m.d 1 2) (by simp) with h2037 | h2037
                                        · linarith only [h0, h2037, hlam]
                                        · rcases p2026_3 (m.d 1 3) (by simp) with h2039 | h2039
                                          · linarith only [h1, h2039, hlam]
                                          · linarith only [h1956, h2039, hlam]
                                      · linarith only [h2036, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      rcases p2026_3 (m.d 0 1) (by simp) with h2043 | h2043
                                      · rcases p2026_3 (m.d 1 2) (by simp) with h2044 | h2044
                                        · linarith only [h0, h2044, hlam]
                                        · rcases p2026_3 (m.d 1 3) (by simp) with h2046 | h2046
                                          · linarith only [h1, h2046, hlam]
                                          · linarith only [h1957, h2046, hlam]
                                      · linarith only [h2043, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h0, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1950, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1952, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1954, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2026_1, u0elo0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1, h1952, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2026_1, u0elo0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p2026_1, u0elo0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h2, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1958, hc12, hc45, hlam, hphi, ht23, ht34, p2026_1]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1956, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1958, hlam, p2026_1]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h3, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2026_1, u0elo0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1957, hlam, p2026_0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [h1, h1947, h1949, h1958, hc14, hlam, hphi, ht0b, ht45, ht5b, p2026_1, u0elo0]
                                    · have p2026_0 := h2026c.1
                                      have p2026_1 := h2026c.2.1
                                      have p2026_2 := h2026c.2.2.1
                                      have p2026_3 := h2026c.2.2.2
                                      linarith only [hlam, p2026_0]
                                  · linarith only [h2025, hlam, p1973_1, u0elo4]
                                  · rcases h1bigk with h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      rcases p2071_3 (m.d 0 1) (by simp) with h2073 | h2073
                                      · rcases p2071_3 (m.d 1 2) (by simp) with h2074 | h2074
                                        · linarith only [h2074, hlam, p2071_0]
                                        · rcases p2071_3 (m.d 1 3) (by simp) with h2076 | h2076
                                          · linarith only [h1, h2076, hlam]
                                          · linarith only [h1950, h2076, hlam]
                                      · linarith only [h2073, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1956, hc34, hlam, hphi, ht0b, ht45, ht5b, p2071_1, u0elo0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      rcases p2071_3 (m.d 0 1) (by simp) with h2081 | h2081
                                      · rcases p2071_3 (m.d 1 2) (by simp) with h2082 | h2082
                                        · linarith only [h0, h2082, hlam]
                                        · rcases p2071_3 (m.d 1 3) (by simp) with h2084 | h2084
                                          · linarith only [h1, h2084, hlam]
                                          · linarith only [h1956, h2084, hlam]
                                      · linarith only [h2081, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      rcases p2071_3 (m.d 0 1) (by simp) with h2088 | h2088
                                      · rcases p2071_3 (m.d 1 2) (by simp) with h2089 | h2089
                                        · linarith only [h0, h2089, hlam]
                                        · rcases p2071_3 (m.d 1 3) (by simp) with h2091 | h2091
                                          · linarith only [h1, h2091, hlam]
                                          · linarith only [h1957, h2091, hlam]
                                      · linarith only [h2088, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h0, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1950, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1952, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1954, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2071_1, u0elo0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1, h1952, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2071_1, u0elo0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p2071_1, u0elo0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h2, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2071_1, u0elo0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1956, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1958, hlam, p2071_1]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h3, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2071_1, u0elo0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1957, hlam, p2071_0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [h1, h1947, h1949, h1958, hc14, hlam, hphi, ht0b, ht45, ht5b, p2071_1, u0elo0]
                                    · have p2071_0 := h2071c.1
                                      have p2071_1 := h2071c.2.1
                                      have p2071_2 := h2071c.2.2.1
                                      have p2071_3 := h2071c.2.2.2
                                      linarith only [hlam, p2071_0]
                                  · rcases h1bigk with h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c | h2115c
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      rcases p2115_3 (m.d 0 1) (by simp) with h2117 | h2117
                                      · rcases p2115_3 (m.d 1 2) (by simp) with h2118 | h2118
                                        · linarith only [h2118, hlam, p2115_0]
                                        · rcases p2115_3 (m.d 1 3) (by simp) with h2120 | h2120
                                          · linarith only [h1, h2120, hlam]
                                          · linarith only [h1950, h2120, hlam]
                                      · linarith only [h2117, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1956, hc34, hlam, hphi, ht0b, ht45, ht5b, p2115_1, u0elo0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      rcases p2115_3 (m.d 0 1) (by simp) with h2125 | h2125
                                      · rcases p2115_3 (m.d 1 2) (by simp) with h2126 | h2126
                                        · linarith only [h0, h2126, hlam]
                                        · rcases p2115_3 (m.d 1 3) (by simp) with h2128 | h2128
                                          · linarith only [h1, h2128, hlam]
                                          · linarith only [h1956, h2128, hlam]
                                      · linarith only [h2125, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      rcases p2115_3 (m.d 0 1) (by simp) with h2132 | h2132
                                      · rcases p2115_3 (m.d 1 2) (by simp) with h2133 | h2133
                                        · linarith only [h0, h2133, hlam]
                                        · rcases p2115_3 (m.d 1 3) (by simp) with h2135 | h2135
                                          · linarith only [h1, h2135, hlam]
                                          · linarith only [h1957, h2135, hlam]
                                      · linarith only [h2132, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h0, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1950, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1952, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1954, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2115_1, u0elo0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1, h1952, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2115_1, u0elo0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p2115_1, u0elo0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h2, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2115_1, u0elo0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1956, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1958, hlam, p2115_1]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h3, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2115_1, u0elo0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1957, hlam, p2115_0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [h1, h1947, h1949, h1958, hc14, hlam, hphi, ht0b, ht45, ht5b, p2115_1, u0elo0]
                                    · have p2115_0 := h2115c.1
                                      have p2115_1 := h2115c.2.1
                                      have p2115_2 := h2115c.2.2.1
                                      have p2115_3 := h2115c.2.2.2
                                      linarith only [hlam, p2115_0]
                                  · rcases h1bigk with h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c | h2159c
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      rcases p2159_3 (m.d 0 1) (by simp) with h2161 | h2161
                                      · rcases p2159_3 (m.d 1 2) (by simp) with h2162 | h2162
                                        · linarith only [h2162, hlam, p2159_0]
                                        · rcases p2159_3 (m.d 1 3) (by simp) with h2164 | h2164
                                          · linarith only [h1, h2164, hlam]
                                          · linarith only [h1950, h2164, hlam]
                                      · linarith only [h2161, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1956, hc34, hlam, hphi, ht0b, ht45, ht5b, p2159_1, u0elo0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      rcases p2159_3 (m.d 0 1) (by simp) with h2169 | h2169
                                      · rcases p2159_3 (m.d 1 2) (by simp) with h2170 | h2170
                                        · linarith only [h0, h2170, hlam]
                                        · rcases p2159_3 (m.d 1 3) (by simp) with h2172 | h2172
                                          · linarith only [h1, h2172, hlam]
                                          · linarith only [h1956, h2172, hlam]
                                      · linarith only [h2169, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      rcases p2159_3 (m.d 0 1) (by simp) with h2176 | h2176
                                      · rcases p2159_3 (m.d 1 2) (by simp) with h2177 | h2177
                                        · linarith only [h0, h2177, hlam]
                                        · rcases p2159_3 (m.d 1 3) (by simp) with h2179 | h2179
                                          · linarith only [h1, h2179, hlam]
                                          · linarith only [h1957, h2179, hlam]
                                      · linarith only [h2176, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h0, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1950, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1952, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1954, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2159_1, u0elo0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1, h1952, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2159_1, u0elo0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p2159_1, u0elo0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h2, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2159_1, u0elo0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1956, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1958, hlam, p2159_1]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h3, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2159_1, u0elo0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1957, hlam, p2159_0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [h1, h1947, h1949, h1958, hc14, hlam, hphi, ht0b, ht45, ht5b, p2159_1, u0elo0]
                                    · have p2159_0 := h2159c.1
                                      have p2159_1 := h2159c.2.1
                                      have p2159_2 := h2159c.2.2.1
                                      have p2159_3 := h2159c.2.2.2
                                      linarith only [hlam, p2159_0]
                                · linarith only [h1819, h2024, hlam]
                              · linarith only [h1304, h2023, hlam]
                            · linarith only [h2022, h4, hlam]
                        · linarith only [h0, h2019, hlam]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1948, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1949, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                  · linarith only [h1304, h1949, h1970, hlam]
                · linarith only [h1948, h1969, h4, hlam]
              · linarith only [h1947, h1949, h1952, h1958, h1968, h4, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1, h1948, h1956, h1957, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2214 | h2214
          · linarith only [h1947, h1956, h2214, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2216 | h2216
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2217 | h2217
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2218 | h2218
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2219 | h2219
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2220 | h2220
                    · rcases h0bigk with h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c | h2221c
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [hlam, p2221_0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        rcases p2221_3 (m.d 0 1) (by simp) with h2223 | h2223
                        · rcases p2221_3 (m.d 0 2) (by simp) with h2224 | h2224
                          · linarith only [h0, h2224, hlam]
                          · rcases p2221_3 (m.d 0 3) (by simp) with h2226 | h2226
                            · linarith only [h1, h2226, hlam]
                            · linarith only [h2226, h4, hlam]
                        · linarith only [h0, h2223, hlam]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1947, h1956, hc14, hlam, hphi, ht0b, ht45, ht5b, p2221_1, u0elo0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1948, h1949, h2214, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2221_1, u0elo0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1948, h2214, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2221_1, u0elo0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h0, hlam, p2221_0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [hlam, p2221_0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h4, hlam, p2221_0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1304, hlam, p2221_1]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1819, hlam, p2221_0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1, hlam, p2221_1]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        rcases p2221_3 (m.d 0 1) (by simp) with h2239 | h2239
                        · rcases p2221_3 (m.d 0 2) (by simp) with h2240 | h2240
                          · linarith only [h2240, h4, hlam]
                          · rcases p2221_3 (m.d 0 3) (by simp) with h2242 | h2242
                            · rcases p2221_3 (m.d 0 4) (by simp) with h2243 | h2243
                              · linarith only [h1947, h2243, hlam]
                              · linarith only [h1304, h2243, hlam]
                            · linarith only [h2242, h4, hlam]
                        · linarith only [h0, h2239, hlam]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [hlam, p2221_0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1, h1948, h1949, h1950, h2214, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2221_1, u0elo0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1, h1948, h1950, h2214, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2221_1, u0elo0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h2, hlam, p2221_0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        rcases p2221_3 (m.d 0 1) (by simp) with h2252 | h2252
                        · rcases p2221_3 (m.d 0 2) (by simp) with h2253 | h2253
                          · linarith only [h1304, h2253, hlam]
                          · rcases p2221_3 (m.d 0 3) (by simp) with h2255 | h2255
                            · rcases p2221_3 (m.d 0 4) (by simp) with h2256 | h2256
                              · rcases p2221_3 (m.d 0 5) (by simp) with h2257 | h2257
                                · linarith only [h1949, h2257, hlam]
                                · linarith only [h1819, h2257, hlam]
                              · linarith only [h1304, h2256, hlam]
                            · linarith only [h2255, h4, hlam]
                        · linarith only [h0, h2252, hlam]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1947, hlam, p2221_0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [hlam, p2221_0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1, h1947, h1948, h1950, h2214, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2221_1, u0elo0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h3, hlam, p2221_0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        rcases p2221_3 (m.d 0 1) (by simp) with h2267 | h2267
                        · rcases p2221_3 (m.d 0 2) (by simp) with h2268 | h2268
                          · linarith only [h1819, h2268, hlam]
                          · rcases p2221_3 (m.d 0 3) (by simp) with h2270 | h2270
                            · rcases p2221_3 (m.d 0 4) (by simp) with h2271 | h2271
                              · rcases p2221_3 (m.d 0 5) (by simp) with h2272 | h2272
                                · rcases h0emin with h2273 | h2273 | h2273 | h2273 | h2273
                                  · rcases h1bigk with h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      rcases p2274_3 (m.d 0 1) (by simp) with h2276 | h2276
                                      · rcases p2274_3 (m.d 1 2) (by simp) with h2277 | h2277
                                        · linarith only [h2277, hlam, p2274_0]
                                        · rcases p2274_3 (m.d 1 3) (by simp) with h2279 | h2279
                                          · linarith only [h1, h2279, hlam]
                                          · linarith only [h1950, h2279, hlam]
                                      · linarith only [h2276, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      rcases p2274_3 (m.d 0 1) (by simp) with h2283 | h2283
                                      · rcases p2274_3 (m.d 1 2) (by simp) with h2284 | h2284
                                        · linarith only [h0, h2284, hlam]
                                        · rcases p2274_3 (m.d 1 3) (by simp) with h2286 | h2286
                                          · linarith only [h2286, hlam, p2274_0]
                                          · rcases p2274_3 (m.d 1 4) (by simp) with h2288 | h2288
                                            · linarith only [h2, h2288, hlam]
                                            · linarith only [h1956, h2288, hlam]
                                      · linarith only [h2283, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h2216, hc45, hlam, hphi, ht0b, ht5b, p2274_1, u0elo0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      rcases p2274_3 (m.d 0 1) (by simp) with h2293 | h2293
                                      · rcases p2274_3 (m.d 1 2) (by simp) with h2294 | h2294
                                        · linarith only [h0, h2294, hlam]
                                        · rcases p2274_3 (m.d 1 3) (by simp) with h2296 | h2296
                                          · linarith only [h1, h2296, hlam]
                                          · rcases p2274_3 (m.d 1 4) (by simp) with h2298 | h2298
                                            · linarith only [h2, h2298, hlam]
                                            · linarith only [h2216, h2298, hlam]
                                      · linarith only [h2293, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h0, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1950, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1952, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1954, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h2214, h2220, hc12, hc34, hlam, hphi, ht23, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1956, hlam, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h2214, hlam, p2274_1]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h2, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2274_1, u0elo0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1, h1947, h1956, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2274_1, u0elo0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1, h1947, h1956, hc15, hlam, hphi, ht0b, ht5b, p2274_1, u0elo0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h3, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2274_1, u0elo0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h1, h1947, h1950, h2214, h2220, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2274_1, u0elo0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [h2216, hlam, p2274_0]
                                    · have p2274_0 := h2274c.1
                                      have p2274_1 := h2274c.2.1
                                      have p2274_2 := h2274c.2.2.1
                                      have p2274_3 := h2274c.2.2.2
                                      linarith only [hlam, p2274_0]
                                  · linarith only [h1, h1947, h1949, h2273, hlam, p2221_1, u0elo0]
                                  · rcases h1bigk with h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c | h2323c
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      rcases p2323_3 (m.d 0 1) (by simp) with h2325 | h2325
                                      · rcases p2323_3 (m.d 1 2) (by simp) with h2326 | h2326
                                        · linarith only [h2326, hlam, p2323_0]
                                        · rcases p2323_3 (m.d 1 3) (by simp) with h2328 | h2328
                                          · linarith only [h1, h2328, hlam]
                                          · linarith only [h1950, h2328, hlam]
                                      · linarith only [h2325, hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      rcases p2323_3 (m.d 0 1) (by simp) with h2332 | h2332
                                      · rcases p2323_3 (m.d 1 2) (by simp) with h2333 | h2333
                                        · linarith only [h0, h2333, hlam]
                                        · rcases p2323_3 (m.d 1 3) (by simp) with h2335 | h2335
                                          · linarith only [h2335, hlam, p2323_0]
                                          · rcases p2323_3 (m.d 1 4) (by simp) with h2337 | h2337
                                            · linarith only [h2, h2337, hlam]
                                            · linarith only [h1956, h2337, hlam]
                                      · linarith only [h2332, hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h2216, hc45, hlam, hphi, ht0b, ht5b, p2323_1, u0elo0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      rcases p2323_3 (m.d 0 1) (by simp) with h2342 | h2342
                                      · rcases p2323_3 (m.d 1 2) (by simp) with h2343 | h2343
                                        · linarith only [h0, h2343, hlam]
                                        · rcases p2323_3 (m.d 1 3) (by simp) with h2345 | h2345
                                          · linarith only [h1, h2345, hlam]
                                          · rcases p2323_3 (m.d 1 4) (by simp) with h2347 | h2347
                                            · linarith only [h2, h2347, hlam]
                                            · linarith only [h2216, h2347, hlam]
                                      · linarith only [h2342, hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h0, hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h1950, hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h1952, hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h1954, hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h1, hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2323_1, u0elo0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h1956, hlam, p2323_1]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h2214, hlam, p2323_1]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h2, hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2323_1, u0elo0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h1, h1947, h1956, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2323_1, u0elo0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h1, h1947, h1956, hc15, hlam, hphi, ht0b, ht5b, p2323_1, u0elo0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h3, hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2323_1, u0elo0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h1, h1947, h1950, h2214, h2220, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2323_1, u0elo0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [h2216, hlam, p2323_0]
                                    · have p2323_0 := h2323c.1
                                      have p2323_1 := h2323c.2.1
                                      have p2323_2 := h2323c.2.2.1
                                      have p2323_3 := h2323c.2.2.2
                                      linarith only [hlam, p2323_0]
                                  · rcases h1bigk with h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c | h2371c
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      rcases p2371_3 (m.d 0 1) (by simp) with h2373 | h2373
                                      · rcases p2371_3 (m.d 1 2) (by simp) with h2374 | h2374
                                        · linarith only [h2374, hlam, p2371_0]
                                        · rcases p2371_3 (m.d 1 3) (by simp) with h2376 | h2376
                                          · linarith only [h1, h2376, hlam]
                                          · linarith only [h1950, h2376, hlam]
                                      · linarith only [h2373, hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      rcases p2371_3 (m.d 0 1) (by simp) with h2380 | h2380
                                      · rcases p2371_3 (m.d 1 2) (by simp) with h2381 | h2381
                                        · linarith only [h0, h2381, hlam]
                                        · rcases p2371_3 (m.d 1 3) (by simp) with h2383 | h2383
                                          · linarith only [h2383, hlam, p2371_0]
                                          · rcases p2371_3 (m.d 1 4) (by simp) with h2385 | h2385
                                            · linarith only [h2, h2385, hlam]
                                            · linarith only [h1956, h2385, hlam]
                                      · linarith only [h2380, hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h2216, hc45, hlam, hphi, ht0b, ht5b, p2371_1, u0elo0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      rcases p2371_3 (m.d 0 1) (by simp) with h2390 | h2390
                                      · rcases p2371_3 (m.d 1 2) (by simp) with h2391 | h2391
                                        · linarith only [h0, h2391, hlam]
                                        · rcases p2371_3 (m.d 1 3) (by simp) with h2393 | h2393
                                          · linarith only [h1, h2393, hlam]
                                          · rcases p2371_3 (m.d 1 4) (by simp) with h2395 | h2395
                                            · linarith only [h2, h2395, hlam]
                                            · linarith only [h2216, h2395, hlam]
                                      · linarith only [h2390, hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h0, hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h1950, hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h1952, hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h1954, hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h1, hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2371_1, u0elo0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h1956, hlam, p2371_1]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h2214, hlam, p2371_1]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h2, hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2371_1, u0elo0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h1, h1947, h1956, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2371_1, u0elo0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h1, h1947, h1956, hc15, hlam, hphi, ht0b, ht5b, p2371_1, u0elo0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h3, hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2371_1, u0elo0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h1, h1947, h1950, h2214, h2220, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2371_1, u0elo0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [h2216, hlam, p2371_0]
                                    · have p2371_0 := h2371c.1
                                      have p2371_1 := h2371c.2.1
                                      have p2371_2 := h2371c.2.2.1
                                      have p2371_3 := h2371c.2.2.2
                                      linarith only [hlam, p2371_0]
                                  · rcases h1bigk with h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c | h2419c
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      rcases p2419_3 (m.d 0 1) (by simp) with h2421 | h2421
                                      · rcases p2419_3 (m.d 1 2) (by simp) with h2422 | h2422
                                        · linarith only [h2422, hlam, p2419_0]
                                        · rcases p2419_3 (m.d 1 3) (by simp) with h2424 | h2424
                                          · linarith only [h1, h2424, hlam]
                                          · linarith only [h1950, h2424, hlam]
                                      · linarith only [h2421, hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      rcases p2419_3 (m.d 0 1) (by simp) with h2428 | h2428
                                      · rcases p2419_3 (m.d 1 2) (by simp) with h2429 | h2429
                                        · linarith only [h0, h2429, hlam]
                                        · rcases p2419_3 (m.d 1 3) (by simp) with h2431 | h2431
                                          · linarith only [h2431, hlam, p2419_0]
                                          · rcases p2419_3 (m.d 1 4) (by simp) with h2433 | h2433
                                            · linarith only [h2, h2433, hlam]
                                            · linarith only [h1956, h2433, hlam]
                                      · linarith only [h2428, hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h2216, hc45, hlam, hphi, ht0b, ht5b, p2419_1, u0elo0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      rcases p2419_3 (m.d 0 1) (by simp) with h2438 | h2438
                                      · rcases p2419_3 (m.d 1 2) (by simp) with h2439 | h2439
                                        · linarith only [h0, h2439, hlam]
                                        · rcases p2419_3 (m.d 1 3) (by simp) with h2441 | h2441
                                          · linarith only [h1, h2441, hlam]
                                          · rcases p2419_3 (m.d 1 4) (by simp) with h2443 | h2443
                                            · linarith only [h2, h2443, hlam]
                                            · linarith only [h2216, h2443, hlam]
                                      · linarith only [h2438, hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h0, hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h1950, hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h1952, hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h1954, hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h1, hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2419_1, u0elo0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h1956, hlam, p2419_1]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h2214, hlam, p2419_1]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h2, hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2419_1, u0elo0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h1, h1947, h1956, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2419_1, u0elo0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h1, h1947, h1956, hc15, hlam, hphi, ht0b, ht5b, p2419_1, u0elo0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h3, hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2419_1, u0elo0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h1, h1947, h1950, h2214, h2220, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2419_1, u0elo0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [h2216, hlam, p2419_0]
                                    · have p2419_0 := h2419c.1
                                      have p2419_1 := h2419c.2.1
                                      have p2419_2 := h2419c.2.2.1
                                      have p2419_3 := h2419c.2.2.2
                                      linarith only [hlam, p2419_0]
                                · linarith only [h1819, h2272, hlam]
                              · linarith only [h1304, h2271, hlam]
                            · linarith only [h2270, h4, hlam]
                        · linarith only [h0, h2267, hlam]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1948, hlam, p2221_0]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [h1949, hlam, p2221_1]
                      · have p2221_0 := h2221c.1
                        have p2221_1 := h2221c.2.1
                        have p2221_2 := h2221c.2.2.1
                        have p2221_3 := h2221c.2.2.2
                        linarith only [hlam, p2221_0]
                    · linarith only [h1, h1947, h1949, h1950, h1956, h2220, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h1304, h2, h2216, h2219, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h1947, h1948, h1956, h2216, h2218, h4, hc45, hlam, hphi, ht0b, ht5b, u0elo4]
              · linarith only [h1947, h2217, h4, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2478 | h2478
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2479 | h2479
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2480 | h2480
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2481 | h2481
                    · linarith only [h1947, h1950, h1956, h2216, h2481, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1949, h1950, h1956, h2481, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1304, h1949, h2480, hlam]
                · linarith only [h1948, h2479, h4, hlam]
              · linarith only [h1947, h2478, h4, hlam]

end R2N4
