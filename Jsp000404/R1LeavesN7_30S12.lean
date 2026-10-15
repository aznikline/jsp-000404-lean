import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5764000 in
set_option maxHeartbeats 5764000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1106 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1991 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1106 := hg1106
  rcases m.htr 0 1 5 (by decide) (by decide) with h1992 | h1992
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1993 | h1993
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1994 | h1994
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1995 | h1995
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1996 | h1996
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1997 | h1997
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1998 | h1998
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1999 | h1999
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2000 | h2000
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2001 | h2001
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2002 | h2002
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2003 | h2003
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2004 | h2004
                          · linarith only [h1991, h2004, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h1106, h1991, h1993, h1998, h2004, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h1106, h1993, h1997, h2003, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1106, h1991, h1993, h1996, h2000, h2002, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1106, h1991, h1995, h1999, h2000, h2001, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h1106, h1994, h1999, h2000, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1993, h1999, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2012 | h2012
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2013 | h2013
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2014 | h2014
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2015 | h2015
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2016 | h2016
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2017 | h2017
                          · linarith only [h1991, h1998, h2017, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2019 | h2019
                            · linarith only [h1993, h2019, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h1993, h1996, h2019, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1106, h1993, h1997, h2016, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1106, h1991, h1993, h1996, h2013, h2015, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1106, h1991, h1995, h2012, h2013, h2014, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h1106, h1994, h2012, h2013, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1993, h2012, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h1106, h1992, h1997, hlam]
          · linarith only [h1106, h1991, h1996, hlam]
        · linarith only [h1106, h1992, h1993, h1995, hlam]
      · linarith only [h1106, h1991, h1993, h1994, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2031 | h2031
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2032 | h2032
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2033 | h2033
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2034 | h2034
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2035 | h2035
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2036 | h2036
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2037 | h2037
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2038 | h2038
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2039 | h2039
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2040 | h2040
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2041 | h2041
                          · linarith only [h1991, h2041, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h0, h1991, h1993, h2035, h2041, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1993, h2034, h2036, h2040, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1991, h1993, h2033, h2036, h2037, h2039, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1991, h1993, h2036, h2037, h2038, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1991, h1993, h2036, h2037, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2048 | h2048
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2049 | h2049
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2050 | h2050
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2051 | h2051
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2052 | h2052
                          · linarith only [h1991, h2052, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h2035, h2052, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h0, h2034, h2036, h2051, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1991, h2033, h2036, h2048, h2050, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1991, h1993, h2032, h2048, h2049, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1993, h2031, h2048, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2059 | h2059
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2060 | h2060
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2061 | h2061
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2062 | h2062
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2063 | h2063
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2064 | h2064
                          · linarith only [h1991, h2035, h2064, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2066 | h2066
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2067 | h2067
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2068 | h2068
                                · linarith only [h0, h1991, h1993, h2035, h2060, h2068, hc05, hlam, hphi, ht0b, ht5b, u0elo2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2070 | h2070
                                  · linarith only [h0, h1992, h1993, h2035, h2060, h2064, h2066, h2070, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · rcases h2bigk with h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [hlam, p2072_0]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h0, hlam, p2072_1]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h1993, hlam, p2072_0]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h1993, h2066, hc34, hlam, hphi, ht0b, ht45, ht5b, p2072_1, u0elo2]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h1993, hc25, hlam, hphi, ht0b, ht5b, p2072_1, u0elo2]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      rcases p2072_3 (m.d 0 2) (by simp) with h2078 | h2078
                                      · linarith only [h0, h2078, hlam]
                                      · rcases p2072_3 (m.d 1 2) (by simp) with h2080 | h2080
                                        · rcases p2072_3 (m.d 2 3) (by simp) with h2081 | h2081
                                          · linarith only [h2059, h2081, hlam]
                                          · linarith only [h1993, h2081, hlam]
                                        · linarith only [h0, h2080, hlam]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [hlam, p2072_0]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h0, h1993, hc01, hc12, hlam, hphi, p2072_1]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h0, h1991, h1993, h2059, h2060, hlam, p2072_2]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h1993, h2032, h2059, hlam, p2072_2]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h0, h1991, h2059, h2060, h2066, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2072_1]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h2059, hlam, p2072_0]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [hlam, p2072_0]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      rcases p2072_3 (m.d 0 2) (by simp) with h2092 | h2092
                                      · linarith only [h1993, h2092, hlam]
                                      · linarith only [h2031, h2092, hlam]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      rcases p2072_3 (m.d 0 2) (by simp) with h2095 | h2095
                                      · linarith only [h1993, h2095, hlam]
                                      · linarith only [h2032, h2095, hlam]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h2031, hlam, p2072_0]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h2060, hlam, p2072_0]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h2066, hlam, p2072_1]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [hlam, p2072_0]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h2068, hlam, p2072_1]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h2032, hlam, p2072_0]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h2061, hlam, p2072_0]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h2067, hlam, p2072_1]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [h1993, h2032, h2059, h2066, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2072_1]
                                    · have p2072_0 := h2072c.1
                                      have p2072_1 := h2072c.2.1
                                      have p2072_2 := h2072c.2.2.1
                                      have p2072_3 := h2072c.2.2.2
                                      linarith only [hlam, p2072_0]
                              · linarith only [h1993, h2034, h2067, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h0, h1993, h2033, h2066, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1991, h1993, h2034, h2059, h2060, h2063, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1991, h1993, h2033, h2059, h2060, h2062, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h2032, h2061, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1993, h2059, h2060, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2114 | h2114
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2115 | h2115
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2116 | h2116
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2117 | h2117
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2118 | h2118
                          · linarith only [h1991, h2035, h2118, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2120 | h2120
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2121 | h2121
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2122 | h2122
                                · linarith only [h1991, h2035, h2114, h2122, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2124 | h2124
                                  · linarith only [h1991, h2035, h2114, h2120, h2124, hlam]
                                  · rcases h2bigk with h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [hlam, p2126_0]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h0, hlam, p2126_1]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h1993, hlam, p2126_0]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h2120, hc34, hlam, hphi, ht0b, ht45, ht5b, p2126_1, u0elo1]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h1993, hc25, hlam, hphi, ht0b, ht5b, p2126_1, u0elo2]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h2059, hc02, hc23, hlam, hphi, p2126_1]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [hlam, p2126_0]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h2059, hlam, p2126_0]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      rcases p2126_3 (m.d 0 2) (by simp) with h2135 | h2135
                                      · linarith only [h0, h2135, hlam]
                                      · linarith only [h2031, h2135, hlam]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      rcases p2126_3 (m.d 0 2) (by simp) with h2138 | h2138
                                      · linarith only [h0, h2138, hlam]
                                      · linarith only [h2032, h2138, hlam]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      rcases p2126_3 (m.d 0 2) (by simp) with h2141 | h2141
                                      · linarith only [h2141, hlam, p2126_0]
                                      · rcases p2126_3 (m.d 1 2) (by simp) with h2143 | h2143
                                        · linarith only [h2059, h2143, hlam]
                                        · linarith only [h0, h2143, hlam]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h0, h1992, h2114, h2118, h2120, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2126_1]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [hlam, p2126_0]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h0, h1992, h2059, h2114, h2118, hlam, p2126_2]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h0, h1992, h2059, h2115, hlam, p2126_2]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h2031, hlam, p2126_0]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h2114, hlam, p2126_0]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h2120, hlam, p2126_1]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [hlam, p2126_0]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h2122, hlam, p2126_1]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h2032, hlam, p2126_0]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h2115, hlam, p2126_0]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h2121, hlam, p2126_1]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [h1992, h2115, h2120, hc34, hlam, hphi, ht0b, ht45, ht5b, p2126_1, u0elo0]
                                    · have p2126_0 := h2126c.1
                                      have p2126_1 := h2126c.2.1
                                      have p2126_2 := h2126c.2.2.1
                                      have p2126_3 := h2126c.2.2.2
                                      linarith only [hlam, p2126_0]
                              · linarith only [h0, h2059, h2121, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h1992, h2059, h2114, h2118, h2120, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h2034, h2059, h2117, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1991, h2033, h2059, h2114, h2116, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1991, h1993, h2032, h2114, h2115, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1991, h1993, h2031, h2114, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · linarith only [h0, h1992, h1993, h2034, hlam]
          · linarith only [h0, h1991, h1993, h2033, hlam]
        · linarith only [h0, h1992, h2032, hlam]
      · linarith only [h0, h1991, h2031, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2170 | h2170
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2171 | h2171
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2172 | h2172
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2173 | h2173
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2174 | h2174
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2175 | h2175
              · linarith only [h1991, h1992, h2175, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2177 | h2177
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2178 | h2178
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2179 | h2179
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2180 | h2180
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2181 | h2181
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2182 | h2182
                          · linarith only [h1991, h1992, h2170, h2174, h2175, h2182, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2184 | h2184
                            · linarith only [h2170, h2184, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h2170, h2173, h2184, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h2170, h2174, h2181, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1106, h2170, h2173, h2180, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1106, h1991, h2172, h2177, h2178, h2179, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h1106, h2171, h2177, h2178, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h1991, h2170, h2177, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2192 | h2192
              · linarith only [h1106, h1991, h2174, h2192, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2194 | h2194
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2195 | h2195
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2196 | h2196
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2197 | h2197
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2198 | h2198
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2199 | h2199
                          · linarith only [h1106, h1991, h2172, h2174, h2192, h2199, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2201 | h2201
                            · linarith only [h2170, h2201, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h2172, h2173, h2174, h2201, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2204 | h2204
                          · linarith only [h1106, h1991, h2172, h2174, h2204, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2206 | h2206
                            · linarith only [h2170, h2206, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h2172, h2173, h2174, h2206, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1106, h2173, h2197, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1106, h1991, h2172, h2194, h2195, h2196, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h1106, h2171, h2194, h2195, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h2170, h2194, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h1106, h1991, h2173, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2214 | h2214
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2215 | h2215
            · linarith only [h2170, h2172, h2215, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2217 | h2217
              · linarith only [h0, h1991, h2172, h2217, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2219 | h2219
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2220 | h2220
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2221 | h2221
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2222 | h2222
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2223 | h2223
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2224 | h2224
                          · linarith only [h1106, h1991, h2170, h2172, h2217, h2224, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2226 | h2226
                            · linarith only [h2170, h2172, h2226, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                            · linarith only [h2170, h2172, h2214, h2226, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2229 | h2229
                          · linarith only [h1106, h1991, h2223, h2229, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2231 | h2231
                            · linarith only [h2170, h2231, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h2170, h2172, h2214, h2231, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h1106, h1991, h2214, h2220, h2222, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2235 | h2235
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2236 | h2236
                        · linarith only [h1106, h1991, h2215, h2219, h2220, h2221, h2236, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2238 | h2238
                          · linarith only [h1991, h2217, h2238, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2240 | h2240
                            · linarith only [h2170, h2172, h2240, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                            · linarith only [h1106, h1991, h2235, h2236, h2240, hc23, hc35, hlam, hphi]
                      · linarith only [h1106, h1991, h2214, h2220, h2235, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h2171, h2172, h2220, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · linarith only [h0, h1991, h2170, h2172, h2219, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
          · linarith only [h1106, h1991, h2214, hlam]
      · linarith only [h0, h1991, h2171, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2248 | h2248
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2249 | h2249
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2250 | h2250
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2251 | h2251
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2252 | h2252
              · linarith only [h1991, h1992, h2252, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2254 | h2254
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2255 | h2255
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2256 | h2256
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2257 | h2257
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2258 | h2258
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2259 | h2259
                          · linarith only [h1991, h2252, h2259, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2261 | h2261
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2262 | h2262
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2263 | h2263
                                · linarith only [h1991, h1992, h2170, h2249, h2255, h2259, h2263, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2265 | h2265
                                  · linarith only [h1991, h1992, h2255, h2259, h2261, h2265, hlam]
                                  · rcases h2bigk with h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c | h2267c
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [hlam, p2267_0]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h0, hlam, p2267_1]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2170, hlam, p2267_0]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2170, hc24, hlam, hphi, ht0b, ht45, ht5b, p2267_1, u0elo2]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2170, hc25, hlam, hphi, ht0b, ht5b, p2267_1, u0elo2]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      rcases p2267_3 (m.d 0 2) (by simp) with h2273 | h2273
                                      · linarith only [h0, h2273, hlam]
                                      · rcases p2267_3 (m.d 1 2) (by simp) with h2275 | h2275
                                        · rcases p2267_3 (m.d 2 3) (by simp) with h2276 | h2276
                                          · linarith only [h2254, h2276, hlam]
                                          · linarith only [h2170, h2276, hlam]
                                        · linarith only [h0, h2275, hlam]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [hlam, p2267_0]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h1992, h2170, h2249, hc01, hc12, hlam, hphi, p2267_1]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2170, h2248, h2254, hlam, p2267_2]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2170, h2249, h2254, hlam, p2267_2]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h1991, h1992, h2249, h2254, h2255, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2267_1]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2254, hlam, p2267_0]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [hlam, p2267_0]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      rcases p2267_3 (m.d 0 2) (by simp) with h2287 | h2287
                                      · linarith only [h2170, h2287, hlam]
                                      · linarith only [h2248, h2287, hlam]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      rcases p2267_3 (m.d 0 2) (by simp) with h2290 | h2290
                                      · linarith only [h2170, h2290, hlam]
                                      · linarith only [h2249, h2290, hlam]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2248, hlam, p2267_0]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2255, hlam, p2267_0]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2261, hlam, p2267_1]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [hlam, p2267_0]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2263, hlam, p2267_1]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2249, hlam, p2267_0]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2256, hlam, p2267_0]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2262, hlam, p2267_1]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [h2249, h2261, hc34, hlam, hphi, ht0b, ht45, ht5b, p2267_1, u0elo1]
                                    · have p2267_0 := h2267c.1
                                      have p2267_1 := h2267c.2.1
                                      have p2267_2 := h2267c.2.2.1
                                      have p2267_3 := h2267c.2.2.2
                                      linarith only [hlam, p2267_0]
                              · linarith only [h2170, h2251, h2262, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1991, h1992, h2170, h2249, h2250, h2255, h2261, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h1991, h1992, h2170, h2249, h2251, h2254, h2255, h2258, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1991, h1992, h2170, h2249, h2250, h2254, h2255, h2257, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h2249, h2256, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h2170, h2254, h2255, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2309 | h2309
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2310 | h2310
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2311 | h2311
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2312 | h2312
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2313 | h2313
                          · linarith only [h1991, h2313, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2315 | h2315
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2316 | h2316
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2317 | h2317
                                · linarith only [h1991, h1992, h2309, h2313, h2317, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2319 | h2319
                                  · linarith only [h1991, h1992, h2309, h2313, h2315, h2319, hlam]
                                  · rcases h2bigk with h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [hlam, p2321_0]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h0, hlam, p2321_1]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2170, hlam, p2321_0]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2315, hc34, hlam, hphi, ht0b, ht45, ht5b, p2321_1, u0elo1]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2170, h2315, h2317, hc34, hlam, hphi, ht0b, ht45, ht5b, p2321_1, u0elo2]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2254, hc02, hc23, hlam, hphi, p2321_1]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [hlam, p2321_0]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2254, hlam, p2321_0]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      rcases p2321_3 (m.d 0 2) (by simp) with h2330 | h2330
                                      · linarith only [h0, h2330, hlam]
                                      · linarith only [h2248, h2330, hlam]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      rcases p2321_3 (m.d 0 2) (by simp) with h2333 | h2333
                                      · linarith only [h0, h2333, hlam]
                                      · linarith only [h2249, h2333, hlam]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      rcases p2321_3 (m.d 0 2) (by simp) with h2336 | h2336
                                      · linarith only [h2336, hlam, p2321_0]
                                      · rcases p2321_3 (m.d 1 2) (by simp) with h2338 | h2338
                                        · linarith only [h2254, h2338, hlam]
                                        · linarith only [h0, h2338, hlam]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h0, h1991, h2309, h2315, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2321_1]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [hlam, p2321_0]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h1991, h1992, h2254, h2309, h2310, hlam, p2321_2]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      rcases p2321_3 (m.d 0 2) (by simp) with h2344 | h2344
                                      · linarith only [h2170, h2344, hlam]
                                      · linarith only [h2249, h2344, hlam]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2248, hlam, p2321_0]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2309, hlam, p2321_0]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2315, hlam, p2321_1]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [hlam, p2321_0]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2317, hlam, p2321_1]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2249, hlam, p2321_0]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2310, hlam, p2321_0]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2316, hlam, p2321_1]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [h2249, h2315, hc34, hlam, hphi, ht0b, ht45, ht5b, p2321_1, u0elo1]
                                    · have p2321_0 := h2321c.1
                                      have p2321_1 := h2321c.2.1
                                      have p2321_2 := h2321c.2.2.1
                                      have p2321_3 := h2321c.2.2.2
                                      linarith only [hlam, p2321_0]
                              · linarith only [h1991, h1992, h2254, h2309, h2310, h2315, h2316, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h1991, h1992, h2254, h2309, h2310, h2315, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h1991, h1992, h2251, h2254, h2309, h2310, h2312, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1991, h1992, h2250, h2254, h2309, h2310, h2311, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h2170, h2249, h2310, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1991, h2170, h2248, h2309, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · linarith only [h2170, h2249, h2251, hlam]
          · linarith only [h0, h1991, h2170, h2250, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2365 | h2365
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2366 | h2366
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2367 | h2367
              · linarith only [h0, h1991, h2249, h2367, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2369 | h2369
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2370 | h2370
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2371 | h2371
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2372 | h2372
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2373 | h2373
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2374 | h2374
                          · linarith only [h0, h1991, h2249, h2366, h2367, h2374, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2376 | h2376
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2377 | h2377
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2378 | h2378
                                · linarith only [h2248, h2249, h2371, h2374, h2378, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2380 | h2380
                                  · linarith only [h0, h2249, h2365, h2371, h2374, h2380, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                  · rcases h2bigk with h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c | h2382c
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [hlam, p2382_0]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h0, hlam, p2382_1]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h2170, hlam, p2382_0]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h2376, hc34, hlam, hphi, ht0b, ht45, ht5b, p2382_1, u0elo1]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h2249, hlam, p2382_0]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      rcases p2382_3 (m.d 0 2) (by simp) with h2388 | h2388
                                      · linarith only [h0, h2388, hlam]
                                      · rcases p2382_3 (m.d 1 2) (by simp) with h2390 | h2390
                                        · rcases p2382_3 (m.d 2 3) (by simp) with h2391 | h2391
                                          · linarith only [h2369, h2391, hlam]
                                          · linarith only [h2170, h2391, hlam]
                                        · linarith only [h0, h2390, hlam]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [hlam, p2382_0]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h0, h1991, h2249, h2370, h2376, h2377, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2382_1]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h0, h1991, h2249, h2369, h2370, h2377, hlam, p2382_2]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h0, h1991, h2249, h2370, h2376, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2382_1]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h0, h1991, h2369, h2370, h2376, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2382_1]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h2369, hlam, p2382_0]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [hlam, p2382_0]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      rcases p2382_3 (m.d 0 2) (by simp) with h2402 | h2402
                                      · linarith only [h2170, h2402, hlam]
                                      · linarith only [h2248, h2402, hlam]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h0, h1991, h2249, h2369, h2370, h2376, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2382_1]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h2248, hlam, p2382_0]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h2370, hlam, p2382_0]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h2376, hlam, p2382_1]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [hlam, p2382_0]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h2378, hlam, p2382_1]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h0, h1991, h2370, h2371, h2374, h2376, hc34, hc45, hlam, hphi, p2382_1]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h2371, hlam, p2382_0]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [h2377, hlam, p2382_1]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      rcases p2382_3 (m.d 0 2) (by simp) with h2414 | h2414
                                      · linarith only [h2249, h2414, hlam]
                                      · linarith only [h2248, h2414, hlam]
                                    · have p2382_0 := h2382c.1
                                      have p2382_1 := h2382c.2.1
                                      have p2382_2 := h2382c.2.2.1
                                      have p2382_3 := h2382c.2.2.2
                                      linarith only [hlam, p2382_0]
                              · linarith only [h2366, h2377, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h0, h1991, h2170, h2365, h2370, h2376, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h2366, h2373, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1991, h2170, h2365, h2369, h2370, h2372, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1991, h2170, h2369, h2370, h2371, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h2170, h2369, h2370, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2424 | h2424
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2425 | h2425
                    · linarith only [h0, h1991, h2249, h2369, h2424, h2425, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2427 | h2427
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2428 | h2428
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2429 | h2429
                          · linarith only [h1991, h2429, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2431 | h2431
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2432 | h2432
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2433 | h2433
                                · linarith only [h0, h1991, h2249, h2366, h2424, h2425, h2429, h2433, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h0, h1991, h2425, h2433, hc14, hc45, hlam, hphi]
                              · linarith only [h0, h1991, h2366, h2369, h2424, h2431, h2432, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h2365, h2369, h2431, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1991, h2366, h2369, h2424, h2428, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1991, h2365, h2369, h2424, h2427, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1991, h2248, h2249, h2424, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2441 | h2441
              · linarith only [h0, h1991, h2170, h2366, h2441, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2443 | h2443
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2444 | h2444
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2445 | h2445
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2446 | h2446
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2447 | h2447
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2448 | h2448
                          · linarith only [h0, h1991, h2170, h2366, h2441, h2443, h2447, h2448, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2450 | h2450
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2451 | h2451
                              · linarith only [h0, h2170, h2366, h2443, h2451, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h1991, h2170, h2444, h2447, h2450, h2451, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h2170, h2365, h2450, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2455 | h2455
                          · linarith only [h1991, h2366, h2441, h2455, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2457 | h2457
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2458 | h2458
                              · linarith only [h2443, h2447, h2458, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2460 | h2460
                                · linarith only [h1991, h2444, h2455, h2460, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2462 | h2462
                                  · linarith only [h0, h1991, h2170, h2444, h2445, h2455, h2457, h2458, h2462, hlam]
                                  · linarith only [h0, h1991, h2170, h2443, h2447, h2462, hc14, hc45, hlam, hphi]
                            · linarith only [h0, h1991, h2170, h2365, h2366, h2444, h2457, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h0, h1991, h2170, h2365, h2366, h2443, h2444, h2446, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h0, h1991, h2170, h2443, h2444, h2445, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1991, h2170, h2443, h2444, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2469 | h2469
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2470 | h2470
                    · linarith only [h0, h1991, h2249, h2443, h2469, h2470, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2472 | h2472
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2473 | h2473
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2474 | h2474
                          · linarith only [h1991, h2474, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2476 | h2476
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2477 | h2477
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2478 | h2478
                                · linarith only [h0, h1991, h2170, h2366, h2443, h2469, h2470, h2473, h2474, h2478, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h1991, h2469, h2470, h2476, h2478, hc34, hc45, hlam, hphi]
                              · linarith only [h2443, h2473, h2477, hlam]
                            · linarith only [h0, h2170, h2366, h2443, h2473, h2476, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2483 | h2483
                          · linarith only [h0, h1991, h2443, h2473, h2483, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2485 | h2485
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2486 | h2486
                              · linarith only [h0, h2443, h2473, h2486, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1991, h2443, h2469, h2485, h2486, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1991, h2443, h2469, h2485, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1991, h2365, h2366, h2443, h2469, h2472, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · linarith only [h0, h2248, h2469, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h1991, h2170, h2365, hlam]
      · linarith only [h0, h1991, h2248, hlam]

set_option maxHeartbeats 5764000 in
set_option maxHeartbeats 5764000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1106 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1991 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2494 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1106 := hg1106
  rcases m.htr 0 2 3 (by decide) (by decide) with h2495 | h2495
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2496 | h2496
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2497 | h2497
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2498 | h2498
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2499 | h2499
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2500 | h2500
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2501 | h2501
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2502 | h2502
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2503 | h2503
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2504 | h2504
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2505 | h2505
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2506 | h2506
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2507 | h2507
                          · linarith only [h2495, h2507, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h2495, h2498, h2507, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1991, h2495, h2498, h2500, h2506, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1991, h2494, h2495, h2499, h2503, h2504, h2505, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h2495, h2498, h2504, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1106, h2497, h2501, h2503, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1106, h2494, h2496, h2501, h2502, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h2495, h2501, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h1991, h2494, h2500, hlam]
          · linarith only [h1106, h2494, h2499, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2518 | h2518
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2519 | h2519
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2520 | h2520
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2521 | h2521
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2522 | h2522
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2523 | h2523
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2524 | h2524
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2525 | h2525
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2526 | h2526
                          · linarith only [h1106, h2495, h2498, h2526, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2528 | h2528
                            · linarith only [h2496, h2526, h2528, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h2518, h2528, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h2498, h2519, h2523, h2525, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h2518, h2524, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2533 | h2533
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2534 | h2534
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2535 | h2535
                          · linarith only [h2495, h2523, h2535, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2537 | h2537
                            · linarith only [h2496, h2535, h2537, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h2496, h2498, h2518, h2537, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1106, h2494, h2496, h2519, h2522, h2523, h2534, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h1106, h2494, h2496, h2498, h2518, h2522, h2533, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h2497, h2522, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1106, h2496, h2520, h2521, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h2494, h2495, h2520, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
            · linarith only [h1106, h2494, h2498, h2519, hlam]
          · linarith only [h1106, h2494, h2518, hlam]
      · linarith only [h0, h2494, h2497, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2548 | h2548
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2549 | h2549
        · linarith only [h2495, h2496, h2549, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2551 | h2551
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2552 | h2552
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2553 | h2553
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2554 | h2554
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2555 | h2555
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2556 | h2556
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2557 | h2557
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2558 | h2558
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2559 | h2559
                          · linarith only [h1106, h2495, h2549, h2559, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2561 | h2561
                            · linarith only [h2495, h2496, h2553, h2556, h2559, h2561, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h2551, h2561, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h2495, h2496, h2554, h2558, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h2549, h2556, h2557, hc03, hc35, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2566 | h2566
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2567 | h2567
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2568 | h2568
                          · linarith only [h1106, h2494, h2555, h2556, h2568, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2570 | h2570
                            · linarith only [h2495, h2496, h2554, h2570, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h2551, h2570, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h2495, h2496, h2554, h2567, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h1106, h2494, h2495, h2551, h2555, h2566, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h2496, h2548, h2555, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2576 | h2576
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2577 | h2577
                    · linarith only [h2549, h2551, h2553, h2554, h2577, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2579 | h2579
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2580 | h2580
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2581 | h2581
                          · linarith only [h2495, h2496, h2577, h2581, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2583 | h2583
                            · linarith only [h2495, h2496, h2583, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                            · linarith only [h2551, h2583, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h2552, h2580, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h1106, h2495, h2496, h2551, h2579, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1106, h2494, h2496, h2548, h2553, h2576, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
              · linarith only [h2495, h2496, h2553, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
            · linarith only [h0, h2494, h2496, h2552, hlam]
          · linarith only [h1106, h2494, h2551, hlam]
      · linarith only [h1106, h2494, h2495, h2548, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2593 | h2593
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2594 | h2594
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2595 | h2595
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2596 | h2596
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2597 | h2597
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2598 | h2598
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2599 | h2599
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2600 | h2600
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2601 | h2601
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2602 | h2602
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2603 | h2603
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2604 | h2604
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2605 | h2605
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2606 | h2606
                              · linarith only [h2593, h2606, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h2495, h2593, h2597, h2606, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h2495, h2596, h2605, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1991, h2494, h2495, h2593, h2595, h2600, h2604, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h2593, h2597, h2603, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h1991, h2495, h2593, h2596, h2598, h2602, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1991, h2494, h2495, h2593, h2595, h2598, h2600, h2601, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h1991, h2494, h2495, h2593, h2598, h2600, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h2495, h2593, h2598, h2599, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2616 | h2616
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2617 | h2617
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2618 | h2618
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2619 | h2619
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2620 | h2620
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2621 | h2621
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2622 | h2622
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2623 | h2623
                              · linarith only [h2593, h2623, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h2597, h2623, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                            · linarith only [h1991, h2494, h2598, h2616, h2617, h2622, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1991, h2494, h2598, h2616, h2617, h2621, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1991, h2494, h2495, h2593, h2597, h2617, h2620, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h2596, h2619, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1991, h2494, h2595, h2598, h2616, h2617, h2618, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h1991, h2495, h2594, h2616, h2617, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2495, h2593, h2616, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h1991, h2494, h2597, hlam]
          · linarith only [h1991, h2494, h2495, h2593, h2596, hlam]
        · linarith only [h2495, h2593, h2595, hlam]
      · linarith only [h1991, h2494, h2593, h2594, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2637 | h2637
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2638 | h2638
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2639 | h2639
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2640 | h2640
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2641 | h2641
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2642 | h2642
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2643 | h2643
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2644 | h2644
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2645 | h2645
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2646 | h2646
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2647 | h2647
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2648 | h2648
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2649 | h2649
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2650 | h2650
                                · linarith only [h2638, h2650, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h2638, h2640, h2650, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · linarith only [h0, h2494, h2593, h2646, h2649, hlam]
                            · linarith only [h0, h2593, h2639, h2647, h2648, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h2638, h2647, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h2494, h2593, h2640, h2642, h2643, h2646, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · linarith only [h0, h2494, h2593, h2639, h2642, h2643, h2644, h2645, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h2638, h2644, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h2494, h2495, h2641, h2643, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h2494, h2495, h2641, h2642, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2661 | h2661
                · linarith only [h0, h2494, h2593, h2641, h2661, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2663 | h2663
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2664 | h2664
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2665 | h2665
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2666 | h2666
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2667 | h2667
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2668 | h2668
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2669 | h2669
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2670 | h2670
                                · linarith only [h2638, h2670, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h2638, h2640, h2670, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · linarith only [h2494, h2661, h2666, h2669, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h0, h2661, h2667, h2668, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h2495, h2638, h2667, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h2494, h2640, h2661, h2663, h2666, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · linarith only [h0, h2494, h2639, h2661, h2663, h2664, h2665, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h2638, h2664, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h2494, h2593, h2637, h2638, h2663, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
            · linarith only [h0, h2494, h2593, h2640, hlam]
          · linarith only [h0, h2494, h2593, h2638, h2639, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2682 | h2682
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2683 | h2683
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2684 | h2684
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2685 | h2685
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2686 | h2686
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2687 | h2687
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2688 | h2688
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2689 | h2689
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2690 | h2690
                          · linarith only [h0, h2495, h2638, h2684, h2690, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h2494, h2495, h2684, h2686, h2687, h2690, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h2683, h2689, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h2682, h2688, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2695 | h2695
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2696 | h2696
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2697 | h2697
                          · linarith only [h2684, h2687, h2697, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2699 | h2699
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2700 | h2700
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2701 | h2701
                                · rcases h2bigk with h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c | h2702c
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h0, hlam, p2702_1]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h2495, hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h2593, hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h2495, h2684, h2687, h2699, h2701, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2702_1]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    rcases p2702_3 (m.d 0 2) (by simp) with h2708 | h2708
                                    · linarith only [h0, h2708, hlam]
                                    · rcases p2702_3 (m.d 1 2) (by simp) with h2710 | h2710
                                      · rcases p2702_3 (m.d 2 3) (by simp) with h2711 | h2711
                                        · linarith only [h2684, h2711, hlam]
                                        · linarith only [h2495, h2711, hlam]
                                      · linarith only [h0, h2710, hlam]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h0, h2494, h2495, h2686, h2699, h2701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2702_1]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h0, h2494, h2495, h2686, h2697, h2699, h2701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2702_1]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h0, h2494, h2495, h2684, h2686, hlam, p2702_2]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h0, h2494, h2684, h2686, h2699, h2701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2702_1]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h2684, hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h2697, hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    rcases p2702_3 (m.d 0 2) (by simp) with h2723 | h2723
                                    · linarith only [h2495, h2723, hlam]
                                    · linarith only [h2637, h2723, hlam]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h0, h2494, h2685, h2686, h2699, h2701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2702_1]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h2685, hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h0, h2494, h2495, h2685, h2686, h2699, h2701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2702_1]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    rcases p2702_3 (m.d 0 2) (by simp) with h2730 | h2730
                                    · linarith only [h2593, h2730, hlam]
                                    · linarith only [h2637, h2730, hlam]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h2637, hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h2686, hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h2699, hlam, p2702_1]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [h2700, hlam, p2702_0]
                                  · have p2702_0 := h2702c.1
                                    have p2702_1 := h2702c.2.1
                                    have p2702_2 := h2702c.2.2.1
                                    have p2702_3 := h2702c.2.2.2
                                    linarith only [hlam, p2702_0]
                                · linarith only [h1106, h2687, h2701, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h2494, h2696, h2700, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h0, h2495, h2638, h2682, h2699, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h2683, h2696, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h2494, h2495, h2682, h2684, h2686, h2695, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h2637, h2686, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h2495, h2684, h2685, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2745 | h2745
                · linarith only [h0, h2494, h2593, h2684, h2745, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2747 | h2747
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2748 | h2748
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2749 | h2749
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2750 | h2750
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2751 | h2751
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2752 | h2752
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2753 | h2753
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2754 | h2754
                                · rcases h2bigk with h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [hlam, p2755_0]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h0, hlam, p2755_1]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h2495, hlam, p2755_0]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h2593, hlam, p2755_0]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h2752, h2754, hc45, hlam, hphi, ht0b, ht5b, p2755_1, u0elo1]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h2745, h2751, hc02, hc23, hlam, hphi, p2755_1]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [hlam, p2755_0]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h2684, hlam, p2755_0]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h2745, hlam, p2755_0]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    rcases p2755_3 (m.d 0 2) (by simp) with h2765 | h2765
                                    · linarith only [h0, h2765, hlam]
                                    · linarith only [h2637, h2765, hlam]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    rcases p2755_3 (m.d 0 2) (by simp) with h2768 | h2768
                                    · linarith only [h2768, hlam, p2755_0]
                                    · rcases p2755_3 (m.d 1 2) (by simp) with h2770 | h2770
                                      · linarith only [h2684, h2770, hlam]
                                      · linarith only [h0, h2770, hlam]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h0, h2494, h2747, h2752, h2754, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2755_1]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [hlam, p2755_0]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h0, h2494, h2593, h2747, h2752, h2754, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2755_1]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h1106, h2494, h2638, h2684, h2747, h2748, hlam, p2755_2]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    rcases p2755_3 (m.d 0 2) (by simp) with h2777 | h2777
                                    · linarith only [h2777, hlam, p2755_0]
                                    · rcases p2755_3 (m.d 1 2) (by simp) with h2779 | h2779
                                      · linarith only [h2745, h2779, hlam]
                                      · linarith only [h0, h2779, hlam]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h0, hc01, hc24, hlam, hphi, ht12, p2755_1]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h2751, hlam, p2755_1]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [hlam, p2755_0]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h0, h2494, h2745, h2747, hlam, p2755_2]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h2637, hlam, p2755_0]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h2747, hlam, p2755_0]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h2752, hlam, p2755_1]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [h2753, hlam, p2755_0]
                                  · have p2755_0 := h2755c.1
                                    have p2755_1 := h2755c.2.1
                                    have p2755_2 := h2755c.2.2.1
                                    have p2755_3 := h2755c.2.2.2
                                    linarith only [hlam, p2755_0]
                                · linarith only [h0, h2495, h2638, h2683, h2754, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h0, h2494, h2745, h2750, h2753, hlam]
                            · linarith only [h2682, h2684, h2752, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h2684, h2748, h2751, hlam]
                        · linarith only [h2683, h2750, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h2638, h2748, h2749, hc03, hc35, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2797 | h2797
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2798 | h2798
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2799 | h2799
                          · linarith only [h1106, h2494, h2747, h2748, h2799, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h2494, h2684, h2747, h2799, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h2494, h2683, h2684, h2747, h2748, h2798, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · linarith only [h0, h2494, h2638, h2682, h2684, h2747, h2797, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h0, h2637, h2747, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h2494, h2495, h2638, h2683, hlam]
          · linarith only [h0, h2494, h2495, h2682, hlam]
      · linarith only [h0, h2494, h2637, hlam]

end R2N4
