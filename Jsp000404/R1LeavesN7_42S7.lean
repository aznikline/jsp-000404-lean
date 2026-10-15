import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1180 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1692 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1845 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1989 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1990 | h1990
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1991 | h1991
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1992 | h1992
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1993 | h1993
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1994 | h1994
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1995 | h1995
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1996 | h1996
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1997 | h1997
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1998 | h1998
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1999 | h1999
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2000 | h2000
                      · linarith only [h1989, h2000, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2002 | h2002
                        · linarith only [h1989, h1992, h2000, h2002, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2004 | h2004
                          · linarith only [h1989, h1992, h2000, h2004, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                          · linarith only [h1989, h1992, h1994, h2004, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                    · linarith only [h1989, h1992, h1994, h1999, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                  · linarith only [h1180, h1989, h1992, h1998, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h1991, h1997, hlam]
              · linarith only [h0, h1990, h1996, hlam]
            · linarith only [h0, h1989, h1995, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2012 | h2012
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2013 | h2013
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2014 | h2014
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2015 | h2015
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2016 | h2016
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2017 | h2017
                      · linarith only [h1989, h2017, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2019 | h2019
                        · linarith only [h1992, h1994, h2012, h2015, h2016, h2017, h2019, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2021 | h2021
                          · linarith only [h1992, h1994, h2017, h2021, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2023 | h2023
                            · linarith only [h1992, h1994, h2023, hlam]
                            · rcases h0bigk with h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [hlam, p2025_0]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h0, hlam, p2025_1]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1180, hlam, p2025_0]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1692, hlam, p2025_1]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1845, hlam, p2025_1]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                rcases p2025_3 (m.d 0 1) (by simp) with h2031 | h2031
                                · linarith only [h0, h2031, hlam]
                                · rcases p2025_3 (m.d 0 2) (by simp) with h2033 | h2033
                                  · rcases p2025_3 (m.d 0 3) (by simp) with h2034 | h2034
                                    · linarith only [h1989, h2034, hlam]
                                    · linarith only [h1180, h2034, hlam]
                                  · linarith only [h0, h2033, hlam]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [hlam, p2025_0]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1993, h2019, hc25, hlam, hphi, ht0b, ht5b, p2025_1, u0elo1]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht45, ht5b, p2025_1, u0elo1, u4ehi0]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1992, h1994, h2017, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2025_1, u0elo1]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                rcases p2025_3 (m.d 0 1) (by simp) with h2042 | h2042
                                · linarith only [h1180, h2042, hlam]
                                · rcases p2025_3 (m.d 0 2) (by simp) with h2044 | h2044
                                  · rcases p2025_3 (m.d 0 3) (by simp) with h2045 | h2045
                                    · rcases p2025_3 (m.d 0 4) (by simp) with h2046 | h2046
                                      · linarith only [h1992, h2046, hlam]
                                      · linarith only [h1692, h2046, hlam]
                                    · linarith only [h1180, h2045, hlam]
                                  · linarith only [h0, h2044, hlam]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1989, hlam, p2025_1]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [hlam, p2025_0]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1989, h1992, h2017, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2025_1, u0elo1]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1989, h1992, h1994, h2017, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2025_1, u0elo1]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1994, h2012, h2015, h2016, hc01, hc12, hlam, hphi, p2025_1]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1990, hlam, p2025_0]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1992, hlam, p2025_0]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [hlam, p2025_0]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1994, hlam, p2025_0]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1994, h2012, h2015, h2016, hc01, hc12, hlam, hphi, p2025_1]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1991, hlam, p2025_1]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1993, hlam, p2025_0]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [h1994, h2012, h2015, h2016, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2025_1, u4ehi0]
                              · have p2025_0 := h2025c.1
                                have p2025_1 := h2025c.2.1
                                have p2025_2 := h2025c.2.2.1
                                have p2025_3 := h2025c.2.2.2
                                linarith only [hlam, p2025_0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2065 | h2065
                      · linarith only [h1989, h2065, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2067 | h2067
                        · linarith only [h1989, h1992, h2065, h2067, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2069 | h2069
                          · linarith only [h1692, h2016, h2069, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2071 | h2071
                            · linarith only [h1692, h1992, h2016, h2071, hlam]
                            · rcases h0bigk with h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [hlam, p2073_0]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h0, hlam, p2073_1]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1180, hlam, p2073_0]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1692, hlam, p2073_1]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1845, hlam, p2073_1]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                rcases p2073_3 (m.d 0 1) (by simp) with h2079 | h2079
                                · linarith only [h0, h2079, hlam]
                                · rcases p2073_3 (m.d 0 2) (by simp) with h2081 | h2081
                                  · rcases p2073_3 (m.d 0 3) (by simp) with h2082 | h2082
                                    · linarith only [h1989, h2082, hlam]
                                    · linarith only [h1180, h2082, hlam]
                                  · linarith only [h0, h2081, hlam]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [hlam, p2073_0]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1993, h2065, h2071, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2073_1, u0elo1]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht45, ht5b, p2073_1, u0elo1, u4ehi0]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1991, h2069, hlam, hphi, ht0b, ht45, ht5b, p2073_1, u0elo1, u4ehi2]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                rcases p2073_3 (m.d 0 1) (by simp) with h2090 | h2090
                                · linarith only [h1180, h2090, hlam]
                                · rcases p2073_3 (m.d 0 2) (by simp) with h2092 | h2092
                                  · rcases p2073_3 (m.d 0 3) (by simp) with h2093 | h2093
                                    · rcases p2073_3 (m.d 0 4) (by simp) with h2094 | h2094
                                      · linarith only [h1992, h2094, hlam]
                                      · linarith only [h1692, h2094, hlam]
                                    · linarith only [h1180, h2093, hlam]
                                  · linarith only [h0, h2092, hlam]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1989, hlam, p2073_1]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [hlam, p2073_0]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1989, h1992, h2065, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2073_1, u0elo1]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1989, h1993, h2065, h2071, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2073_1, u0elo1]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1692, h2016, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2073_1]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1990, hlam, p2073_0]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1992, hlam, p2073_0]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [hlam, p2073_0]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1994, hlam, p2073_0]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                rcases p2073_3 (m.d 0 1) (by simp) with h2108 | h2108
                                · linarith only [h1845, h2108, hlam]
                                · rcases p2073_3 (m.d 0 2) (by simp) with h2110 | h2110
                                  · rcases p2073_3 (m.d 0 3) (by simp) with h2111 | h2111
                                    · rcases p2073_3 (m.d 0 4) (by simp) with h2112 | h2112
                                      · linarith only [h1994, h2112, hlam]
                                      · linarith only [h1692, h2112, hlam]
                                    · linarith only [h1180, h2111, hlam]
                                  · linarith only [h0, h2110, hlam]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1991, hlam, p2073_1]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [h1993, hlam, p2073_0]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht45, ht5b, p2073_1, u0elo4, u4ehi0]
                              · have p2073_0 := h2073c.1
                                have p2073_1 := h2073c.2.1
                                have p2073_2 := h2073c.2.2.1
                                have p2073_3 := h2073c.2.2.2
                                linarith only [hlam, p2073_0]
                  · linarith only [h1180, h1992, h2015, hlam]
                · linarith only [h0, h1991, h2014, hlam]
              · linarith only [h0, h1990, h2013, hlam]
            · linarith only [h0, h1989, h2012, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2125 | h2125
          · linarith only [h1992, h1993, h2125, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2127 | h2127
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2128 | h2128
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2129 | h2129
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2130 | h2130
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2131 | h2131
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2132 | h2132
                      · linarith only [h1989, h2132, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                      · linarith only [h1992, h1993, h2132, hc23, hc35, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2135 | h2135
                      · linarith only [h1989, h2135, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                      · linarith only [h1992, h1993, h2135, hc23, hc35, hlam, hphi]
                  · linarith only [h1180, h1992, h2130, hlam]
                · linarith only [h0, h1991, h2129, hlam]
              · linarith only [h0, h1989, h1990, h1992, h2128, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · linarith only [h0, h1989, h2127, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2142 | h2142
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2143 | h2143
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2144 | h2144
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2145 | h2145
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2146 | h2146
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2147 | h2147
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2148 | h2148
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2149 | h2149
                      · linarith only [h1989, h1992, h2149, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2151 | h2151
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2152 | h2152
                          · linarith only [h1990, h2152, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                          · linarith only [h2143, h2152, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                        · linarith only [h1992, h2142, h2144, h2147, h2151, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1992, h2142, h2143, h2147, h2148, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2157 | h2157
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2158 | h2158
                      · linarith only [h1989, h2158, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2160 | h2160
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2161 | h2161
                          · linarith only [h1990, h2161, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                          · linarith only [h2143, h2161, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                        · linarith only [h1180, h2142, h2147, h2160, hc23, hc34, hlam, hphi]
                    · linarith only [h1990, h2143, h2157, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                · linarith only [h0, h1991, h2146, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1990, h2145, hlam]
            · linarith only [h0, h1989, h2144, hlam]
          · linarith only [h1992, h2142, h2143, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2170 | h2170
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2171 | h2171
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2172 | h2172
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2173 | h2173
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2174 | h2174
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2175 | h2175
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2176 | h2176
                      · linarith only [h1989, h1992, h2176, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2178 | h2178
                        · linarith only [h1989, h2142, h2178, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2180 | h2180
                          · linarith only [h1990, h2180, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                          · linarith only [h2170, h2180, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                    · linarith only [h1992, h2170, h2174, h2175, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2184 | h2184
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2185 | h2185
                      · linarith only [h1180, h1989, h2174, h2185, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2187 | h2187
                        · linarith only [h1180, h1989, h2142, h2187, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2189 | h2189
                          · linarith only [h1990, h2189, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                          · linarith only [h2170, h2189, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                    · linarith only [h1692, h2170, h2184, hlam]
                · linarith only [h0, h1991, h2173, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1990, h2172, hlam]
            · linarith only [h0, h1989, h1990, h2171, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2196 | h2196
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2197 | h2197
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2198 | h2198
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2199 | h2199
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2200 | h2200
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2201 | h2201
                      · linarith only [h1989, h2201, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2203 | h2203
                        · linarith only [h1845, h1989, h1992, h2142, h2170, h2196, h2199, h2200, h2203, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2205 | h2205
                          · linarith only [h1990, h1992, h2170, h2205, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2207 | h2207
                            · linarith only [h1990, h2170, h2196, h2199, h2207, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h1180, h1992, h2200, h2207, hc01, hc14, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2210 | h2210
                      · linarith only [h1989, h1992, h2210, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2212 | h2212
                        · linarith only [h1989, h2142, h2212, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2214 | h2214
                          · linarith only [h1990, h2200, h2214, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2216 | h2216
                            · linarith only [h2199, h2200, h2216, hlam]
                            · rcases h0bigk with h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c | h2218c
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [hlam, p2218_0]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h0, hlam, p2218_1]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h1180, hlam, p2218_0]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h1692, hlam, p2218_1]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h1845, hlam, p2218_1]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                rcases p2218_3 (m.d 0 1) (by simp) with h2224 | h2224
                                · linarith only [h0, h2224, hlam]
                                · rcases p2218_3 (m.d 0 2) (by simp) with h2226 | h2226
                                  · rcases p2218_3 (m.d 0 3) (by simp) with h2227 | h2227
                                    · linarith only [h1989, h2227, hlam]
                                    · linarith only [h1180, h2227, hlam]
                                  · linarith only [h0, h2226, hlam]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [hlam, p2218_0]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                rcases p2218_3 (m.d 0 1) (by simp) with h2232 | h2232
                                · linarith only [h0, h2232, hlam]
                                · rcases p2218_3 (m.d 0 2) (by simp) with h2234 | h2234
                                  · rcases p2218_3 (m.d 0 3) (by simp) with h2235 | h2235
                                    · linarith only [h1989, h2235, hlam]
                                    · rcases p2218_3 (m.d 0 4) (by simp) with h2237 | h2237
                                      · linarith only [h1990, h2237, hlam]
                                      · linarith only [h1992, h2237, hlam]
                                  · linarith only [h1989, h2234, hlam]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht45, ht5b, p2218_1, u0elo1, u4ehi0]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h1990, h2170, hlam, hphi, ht0b, ht45, ht5b, p2218_1, u0elo1, u4ehi2]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h2142, hc01, hc35, hlam, hphi, ht12, ht23, p2218_1]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h1989, hlam, p2218_1]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [hlam, p2218_0]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h1992, hlam, p2218_1]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h2142, hlam, p2218_1]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h1692, h2200, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2218_1]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h1990, hlam, p2218_0]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h1992, h2199, h2200, hc03, hc45, hlam, hphi, ht34, p2218_1]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [hlam, p2218_0]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h2170, hlam, p2218_0]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                rcases p2218_3 (m.d 0 1) (by simp) with h2253 | h2253
                                · linarith only [h1845, h2253, hlam]
                                · rcases p2218_3 (m.d 0 2) (by simp) with h2255 | h2255
                                  · rcases p2218_3 (m.d 0 3) (by simp) with h2256 | h2256
                                    · linarith only [h2142, h2256, hlam]
                                    · linarith only [h1180, h2256, hlam]
                                  · linarith only [h0, h2255, hlam]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [h1991, hlam, p2218_1]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                rcases p2218_3 (m.d 0 1) (by simp) with h2261 | h2261
                                · linarith only [h1845, h2261, hlam]
                                · rcases p2218_3 (m.d 0 2) (by simp) with h2263 | h2263
                                  · rcases p2218_3 (m.d 0 3) (by simp) with h2264 | h2264
                                    · linarith only [h2142, h2264, hlam]
                                    · rcases p2218_3 (m.d 0 4) (by simp) with h2266 | h2266
                                      · linarith only [h2170, h2266, hlam]
                                      · linarith only [h1992, h2266, hlam]
                                  · linarith only [h1989, h2263, hlam]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht45, ht5b, p2218_1, u0elo4, u4ehi0]
                              · have p2218_0 := h2218c.1
                                have p2218_1 := h2218c.2.1
                                have p2218_2 := h2218c.2.2.1
                                have p2218_3 := h2218c.2.2.2
                                linarith only [hlam, p2218_0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2272 | h2272
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2273 | h2273
                      · linarith only [h1990, h2170, h2199, h2272, h2273, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2275 | h2275
                        · linarith only [h1989, h2142, h2275, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2277 | h2277
                          · linarith only [h1990, h2170, h2277, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2279 | h2279
                            · rcases h0bigk with h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c | h2280c
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [hlam, p2280_0]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h0, hlam, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h1180, hlam, p2280_0]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h1692, hlam, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h1845, hlam, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                rcases p2280_3 (m.d 0 1) (by simp) with h2286 | h2286
                                · linarith only [h0, h2286, hlam]
                                · rcases p2280_3 (m.d 0 2) (by simp) with h2288 | h2288
                                  · rcases p2280_3 (m.d 0 3) (by simp) with h2289 | h2289
                                    · linarith only [h1989, h2289, hlam]
                                    · linarith only [h1180, h2289, hlam]
                                  · linarith only [h0, h2288, hlam]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [hlam, p2280_0]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                rcases p2280_3 (m.d 0 1) (by simp) with h2294 | h2294
                                · linarith only [h0, h2294, hlam]
                                · rcases p2280_3 (m.d 0 2) (by simp) with h2296 | h2296
                                  · rcases p2280_3 (m.d 0 3) (by simp) with h2297 | h2297
                                    · linarith only [h1989, h2297, hlam]
                                    · rcases p2280_3 (m.d 0 4) (by simp) with h2299 | h2299
                                      · linarith only [h1990, h2299, hlam]
                                      · linarith only [h1992, h2299, hlam]
                                  · linarith only [h1989, h2296, hlam]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h1990, hlam, hphi, ht0b, ht45, ht5b, p2280_1, u0elo1, u4ehi2]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h1990, h2170, hlam, hphi, ht0b, ht45, ht5b, p2280_1, u0elo1, u4ehi2]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h1180, h2199, hc01, hc34, hlam, hphi, ht12, ht23, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h1989, hlam, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [hlam, p2280_0]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h1992, hlam, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h2142, hlam, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h2170, h2199, h2272, hc01, hc34, hlam, hphi, ht12, ht23, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h1990, hlam, p2280_0]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h2170, h2199, h2272, hc03, hc34, hlam, hphi, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [hlam, p2280_0]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h2170, hlam, p2280_0]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h2170, h2199, h2272, hc01, hc34, hlam, hphi, ht12, ht23, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h1991, hlam, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h2170, h2199, h2272, hc03, hc34, hlam, hphi, p2280_1]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [h1990, h2170, h2199, h2272, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2280_1, u4ehi2]
                              · have p2280_0 := h2280c.1
                                have p2280_1 := h2280c.2.1
                                have p2280_2 := h2280c.2.2.1
                                have p2280_3 := h2280c.2.2.2
                                linarith only [hlam, p2280_0]
                            · linarith only [h2199, h2272, h2279, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2321 | h2321
                      · linarith only [h1989, h2321, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2323 | h2323
                        · linarith only [h1989, h2142, h2323, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2325 | h2325
                          · linarith only [h1180, h1990, h2199, h2272, h2325, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2327 | h2327
                            · linarith only [h1180, h2199, h2272, h2327, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1180, h2199, h2327, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h1991, h2198, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1990, h2197, hlam]
            · linarith only [h0, h1989, h1992, h2196, hc01, hc34, hlam, hphi, ht12, ht23]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2333 | h2333
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2334 | h2334
        · linarith only [h1989, h1991, h2334, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2336 | h2336
          · linarith only [h1989, h1991, h2333, h2336, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2338 | h2338
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2339 | h2339
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2340 | h2340
                · linarith only [h1990, h1991, h2340, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2342 | h2342
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2343 | h2343
                    · linarith only [h2336, h2339, h2340, h2343, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2345 | h2345
                      · linarith only [h1989, h2345, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                      · linarith only [h2333, h2334, h2345, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1180, h1990, h2333, h2340, h2342, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h1990, h2339, hlam]
            · linarith only [h0, h1989, h2338, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2351 | h2351
        · linarith only [h1989, h1991, h2351, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2353 | h2353
          · linarith only [h1990, h1991, h2353, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2355 | h2355
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2356 | h2356
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2357 | h2357
                · linarith only [h1990, h1991, h2357, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2359 | h2359
                  · linarith only [h1180, h2333, h2355, h2357, h2359, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2361 | h2361
                    · linarith only [h2353, h2356, h2357, h2361, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2363 | h2363
                      · linarith only [h1180, h1989, h2359, h2363, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2365 | h2365
                        · linarith only [h1989, h1990, h1991, h2351, h2365, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2367 | h2367
                          · linarith only [h0, h1180, h1990, h2357, h2359, h2361, h2365, h2367, hc03, hc35, hlam, hphi]
                          · linarith only [h0, h1990, h2357, h2367, hc45, hlam, hphi, u4ehi2]
              · linarith only [h0, h1990, h2356, hlam]
            · linarith only [h0, h1989, h1990, h2355, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2372 | h2372
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2373 | h2373
      · linarith only [h1989, h1990, h2373, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2375 | h2375
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2376 | h2376
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2377 | h2377
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2378 | h2378
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2379 | h2379
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2380 | h2380
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2381 | h2381
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2382 | h2382
                      · linarith only [h1989, h1990, h2373, h2378, h2382, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2384 | h2384
                        · linarith only [h1989, h1990, h2377, h2380, h2382, h2384, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1989, h1990, h2375, h2377, h2380, h2382, h2384, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2376, h2381, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2388 | h2388
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2389 | h2389
                      · linarith only [h1180, h2380, h2389, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2391 | h2391
                        · linarith only [h1989, h1990, h2378, h2391, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1989, h1990, h2375, h2378, h2391, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1989, h1990, h2375, h2376, h2378, h2388, hlam]
                · linarith only [h1990, h2378, h2379, hc02, hc25, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2396 | h2396
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2397 | h2397
                  · linarith only [h2373, h2375, h2376, h2377, h2378, h2397, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2399 | h2399
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2400 | h2400
                      · linarith only [h1989, h2397, h2400, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2402 | h2402
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2403 | h2403
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2404 | h2404
                            · linarith only [h0, h1989, h2378, h2400, h2402, h2404, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h1989, h2378, h2400, h2404, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h1989, h2375, h2376, h2378, h2402, h2403, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h0, h1989, h2375, h2378, h2400, h2402, hc23, hc34, hlam, hphi]
                    · linarith only [h1692, h2376, h2399, hlam]
                · linarith only [h0, h2372, h2396, hlam]
            · linarith only [h0, h1989, h2377, hlam]
          · linarith only [h1989, h1990, h2375, h2376, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2413 | h2413
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2414 | h2414
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2415 | h2415
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2416 | h2416
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2417 | h2417
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2418 | h2418
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2419 | h2419
                      · linarith only [h1989, h1990, h2373, h2413, h2415, h2419, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2421 | h2421
                        · linarith only [h1180, h1989, h1990, h2375, h2414, h2417, h2419, h2421, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2423 | h2423
                          · linarith only [h1990, h2372, h2414, h2417, h2419, h2423, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h1990, h2413, h2423, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1692, h1990, h2372, h2413, h2418, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2427 | h2427
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2428 | h2428
                      · linarith only [h1180, h2417, h2428, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2430 | h2430
                        · linarith only [h1180, h1989, h1990, h2375, h2415, h2430, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2432 | h2432
                          · linarith only [h1990, h2372, h2415, h2432, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h1990, h2413, h2432, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1990, h2372, h2413, h2415, h2427, hlam]
                · linarith only [h1990, h2415, h2416, hc02, hc25, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2437 | h2437
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2438 | h2438
                  · linarith only [h1180, h2373, h2414, h2415, h2438, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2440 | h2440
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2441 | h2441
                      · linarith only [h1989, h2438, h2441, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2443 | h2443
                        · linarith only [h1989, h2375, h2443, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2445 | h2445
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2446 | h2446
                            · rcases h0bigk with h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [hlam, p2447_0]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h0, hlam, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h1180, hlam, p2447_0]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h1692, hlam, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h1845, hlam, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h0, h2415, h2441, hc01, hc34, hlam, hphi, ht12, ht23, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [hlam, p2447_0]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h0, h1180, h2415, h2441, hc01, hc34, hlam, hphi, ht12, ht23, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h1990, hlam, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h0, h2372, h2415, h2441, h2445, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2447_1, u4ehi4]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h2375, hc01, hc35, hlam, hphi, ht12, ht23, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h1989, hlam, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [hlam, p2447_0]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h2373, hlam, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h2375, hlam, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                rcases p2447_3 (m.d 0 1) (by simp) with h2463 | h2463
                                · linarith only [h1692, h2463, hlam]
                                · rcases p2447_3 (m.d 0 2) (by simp) with h2465 | h2465
                                  · linarith only [h1990, h2465, hlam]
                                  · linarith only [h0, h2465, hlam]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h1989, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2447_1, u0elo3]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                rcases p2447_3 (m.d 0 1) (by simp) with h2469 | h2469
                                · linarith only [h1692, h2469, hlam]
                                · rcases p2447_3 (m.d 0 2) (by simp) with h2471 | h2471
                                  · linarith only [h1990, h2471, hlam]
                                  · linarith only [h1989, h2471, hlam]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [hlam, p2447_0]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h2372, h2445, hlam, hphi, ht0b, ht45, ht5b, p2447_1, u0elo3, u4ehi4]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h0, h2372, h2415, h2441, hc01, hc34, hlam, hphi, ht12, ht23, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h2372, hlam, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h0, h2372, h2415, h2441, hc03, hc34, hlam, hphi, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [h2413, hlam, p2447_1]
                              · have p2447_0 := h2447c.1
                                have p2447_1 := h2447c.2.1
                                have p2447_2 := h2447c.2.2.1
                                have p2447_3 := h2447c.2.2.2
                                linarith only [hlam, p2447_0]
                            · linarith only [h0, h2372, h2415, h2441, h2445, h2446, hlam]
                          · linarith only [h0, h2415, h2445, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h2413, h2440, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                · linarith only [h0, h2372, h2437, hlam]
            · linarith only [h0, h1989, h2414, hlam]
          · linarith only [h1990, h2372, h2413, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2487 | h2487
      · linarith only [h1989, h1990, h2487, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2489 | h2489
        · linarith only [h1989, h2372, h2489, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2491 | h2491
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2492 | h2492
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2493 | h2493
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2494 | h2494
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2495 | h2495
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2496 | h2496
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2497 | h2497
                      · linarith only [h1989, h1990, h2487, h2493, h2497, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2499 | h2499
                        · linarith only [h1989, h1990, h2489, h2492, h2495, h2497, h2499, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2501 | h2501
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2502 | h2502
                            · rcases h0bigk with h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [hlam, p2503_0]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h0, hlam, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1180, hlam, p2503_0]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1692, hlam, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1845, hlam, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h2372, h2492, h2495, h2497, h2501, hc01, hc12, hlam, hphi, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [hlam, p2503_0]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1180, h2372, h2492, h2495, h2497, h2501, hc01, hc12, hlam, hphi, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1990, hlam, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h2372, hlam, p2503_0]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1989, h2372, h2492, h2495, h2497, h2501, hc01, hc12, hlam, hphi, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1989, hlam, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [hlam, p2503_0]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h2487, hlam, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h2489, hlam, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1990, h2492, h2495, h2497, hc01, hc12, hlam, hphi, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1989, h1990, h2492, h2495, h2497, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1180, h1990, h2492, h2495, h2497, hc01, hc12, hlam, hphi, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [hlam, p2503_0]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1989, h1990, h2372, h2492, h2495, h2497, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h2372, h2492, h2495, h2497, h2501, hc01, hc12, hlam, hphi, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1989, h2372, h2492, h2495, h2497, h2501, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h1180, h2372, h2492, h2495, h2497, h2501, hc01, hc12, hlam, hphi, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [h2491, hlam, p2503_1]
                              · have p2503_0 := h2503c.1
                                have p2503_1 := h2503c.2.1
                                have p2503_2 := h2503c.2.2.1
                                have p2503_3 := h2503c.2.2.2
                                linarith only [hlam, p2503_0]
                            · linarith only [h1990, h2491, h2497, h2502, hlam]
                          · linarith only [h1990, h2491, h2501, hlam]
                    · linarith only [h2491, h2496, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2532 | h2532
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2533 | h2533
                      · linarith only [h1989, h2495, h2533, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2535 | h2535
                        · linarith only [h1989, h1990, h2493, h2535, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2537 | h2537
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2538 | h2538
                            · rcases h0bigk with h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c | h2539c
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [hlam, p2539_0]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h0, hlam, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1180, hlam, p2539_0]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1692, hlam, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1845, hlam, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h2372, h2493, h2537, hc01, hc12, hlam, hphi, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [hlam, p2539_0]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1180, h2372, h2493, h2537, hc01, hc12, hlam, hphi, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1990, hlam, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h2372, hlam, p2539_0]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1989, h2372, h2493, h2537, hc01, hc12, hlam, hphi, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1989, hlam, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [hlam, p2539_0]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h2487, hlam, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h2489, hlam, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1990, h2493, hc01, hc12, hlam, hphi, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1989, h1990, h2493, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1180, h1990, h2493, hc01, hc12, hlam, hphi, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [hlam, p2539_0]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1845, h1990, h2493, hc01, hc12, hlam, hphi, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h2372, h2493, h2537, hc01, hc12, hlam, hphi, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1989, h2372, h2493, h2537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h1180, h2372, h2493, h2537, hc01, hc12, hlam, hphi, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [h2491, hlam, p2539_1]
                              · have p2539_0 := h2539c.1
                                have p2539_1 := h2539c.2.1
                                have p2539_2 := h2539c.2.2.1
                                have p2539_3 := h2539c.2.2.2
                                linarith only [hlam, p2539_0]
                            · linarith only [h1990, h2491, h2493, h2495, h2538, hlam]
                          · linarith only [h1990, h2491, h2537, hlam]
                    · linarith only [h1990, h2491, h2493, h2532, hlam]
                · linarith only [h1990, h2491, h2493, h2494, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2569 | h2569
                · linarith only [h1989, h2372, h2493, h2569, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2571 | h2571
                  · linarith only [h1180, h2487, h2492, h2493, h2571, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2573 | h2573
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2574 | h2574
                      · linarith only [h1180, h2571, h2574, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2576 | h2576
                        · linarith only [h0, h1989, h2489, h2493, h2574, h2576, hc03, hc34, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2578 | h2578
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2579 | h2579
                            · rcases h0bigk with h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [hlam, p2580_0]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h0, hlam, p2580_1]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h1180, hlam, p2580_0]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h1692, hlam, p2580_1]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h1845, hlam, p2580_1]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h0, h2569, h2574, h2578, hc01, hc34, hlam, hphi, ht12, ht23, p2580_1]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [hlam, p2580_0]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h0, h1180, h2569, h2574, h2578, hc01, hc34, hlam, hphi, ht12, ht23, p2580_1]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h1990, hlam, p2580_1]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h2372, hlam, p2580_0]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h1180, h2492, h2569, h2574, h2578, hc01, hc34, hlam, hphi, ht12, ht23, p2580_1]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h1989, hlam, p2580_1]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [hlam, p2580_0]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h2487, hlam, p2580_1]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h2489, hlam, p2580_1]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                rcases p2580_3 (m.d 0 1) (by simp) with h2596 | h2596
                                · linarith only [h1692, h2596, hlam]
                                · rcases p2580_3 (m.d 0 2) (by simp) with h2598 | h2598
                                  · linarith only [h1990, h2598, hlam]
                                  · linarith only [h0, h2598, hlam]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h1989, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2580_1, u0elo3]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                rcases p2580_3 (m.d 0 1) (by simp) with h2602 | h2602
                                · linarith only [h1692, h2602, hlam]
                                · rcases p2580_3 (m.d 0 2) (by simp) with h2604 | h2604
                                  · linarith only [h1990, h2604, hlam]
                                  · linarith only [h1989, h2604, hlam]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [hlam, p2580_0]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h1989, h2372, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2580_1, u0elo3]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                rcases p2580_3 (m.d 0 1) (by simp) with h2609 | h2609
                                · linarith only [h1845, h2609, hlam]
                                · rcases p2580_3 (m.d 0 2) (by simp) with h2611 | h2611
                                  · linarith only [h2372, h2611, hlam]
                                  · linarith only [h0, h2611, hlam]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h1989, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2580_1, u0elo4]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                rcases p2580_3 (m.d 0 1) (by simp) with h2615 | h2615
                                · linarith only [h1845, h2615, hlam]
                                · rcases p2580_3 (m.d 0 2) (by simp) with h2617 | h2617
                                  · linarith only [h2372, h2617, hlam]
                                  · linarith only [h1989, h2617, hlam]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [h2491, hlam, p2580_1]
                              · have p2580_0 := h2580c.1
                                have p2580_1 := h2580c.2.1
                                have p2580_2 := h2580c.2.2.1
                                have p2580_3 := h2580c.2.2.2
                                linarith only [hlam, p2580_0]
                            · linarith only [h2491, h2569, h2574, h2578, h2579, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1180, h2491, h2492, h2493, h2578, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1692, h2491, h2573, hlam]
            · linarith only [h0, h1989, h2492, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2626 | h2626
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2627 | h2627
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2628 | h2628
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2629 | h2629
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2630 | h2630
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2631 | h2631
                      · linarith only [h1180, h1989, h1990, h2487, h2491, h2626, h2629, h2630, h2631, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2633 | h2633
                        · linarith only [h1989, h1990, h2489, h2491, h2626, h2629, h2630, h2633, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2635 | h2635
                          · linarith only [h1989, h1990, h2491, h2631, h2635, hc23, hc34, hlam, hphi]
                          · linarith only [h1989, h1990, h2626, h2629, h2630, h2635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1989, h1990, h2627, h2630, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2639 | h2639
                    · linarith only [h1989, h1990, h2491, h2629, h2639, hc23, hc34, hlam, hphi]
                    · linarith only [h1989, h1990, h2627, h2639, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1989, h1990, h2627, h2628, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2643 | h2643
                · linarith only [h1989, h2372, h2627, h2643, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2645 | h2645
                  · linarith only [h1180, h2487, h2626, h2627, h2645, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2647 | h2647
                    · linarith only [h1989, h1990, h2491, h2645, h2647, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2649 | h2649
                      · linarith only [h1989, h2649, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2651 | h2651
                        · linarith only [h0, h1845, h1989, h2489, h2627, h2647, h2651, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2653 | h2653
                          · linarith only [h0, h1989, h2627, h2647, h2649, h2653, hc23, hc34, hlam, hphi]
                          · linarith only [h1989, h1990, h2653, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h1989, h1990, h2626, hc12, hc24, hlam, hphi]

end R2N4
