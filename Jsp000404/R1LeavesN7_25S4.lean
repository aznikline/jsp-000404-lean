import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 5 (by decide) (by decide) with h1984 | h1984
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1985 | h1985
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1986 | h1986
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1987 | h1987
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1988 | h1988
          · linarith only [h1988, h5, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1990 | h1990
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1991 | h1991
              · linarith only [h1984, h1985, h1991, h5, hc12, hlam, hphi, ht01, u0ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1993 | h1993
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1994 | h1994
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1995 | h1995
                    · rcases h2bigk with h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h0, h1986, h1991, h1993, hc01, hc35, hlam, hphi, ht0b, ht5b, p1996_1]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        rcases p1996_3 (m.d 0 2) (by simp) with h1999 | h1999
                        · rcases p1996_3 (m.d 1 2) (by simp) with h2000 | h2000
                          · linarith only [h0, h2000, hlam]
                          · linarith only [h1985, h2000, hlam]
                        · linarith only [h1999, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        rcases p1996_3 (m.d 0 2) (by simp) with h2004 | h2004
                        · rcases p1996_3 (m.d 1 2) (by simp) with h2005 | h2005
                          · linarith only [h0, h2005, hlam]
                          · linarith only [h1986, h2005, hlam]
                        · linarith only [h2004, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        rcases p1996_3 (m.d 0 2) (by simp) with h2009 | h2009
                        · rcases p1996_3 (m.d 1 2) (by simp) with h2010 | h2010
                          · linarith only [h0, h2010, hlam]
                          · linarith only [h1987, h2010, hlam]
                        · linarith only [h2009, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h0, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h0, h1993, h1995, hc01, hc45, hlam, hphi, ht0b, ht5b, p1996_1]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h0, h1991, h1993, h1995, hc01, hc45, hlam, hphi, ht0b, ht5b, p1996_1]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        rcases p1996_3 (m.d 0 2) (by simp) with h2018 | h2018
                        · rcases p1996_3 (m.d 1 2) (by simp) with h2019 | h2019
                          · rcases p1996_3 (m.d 2 3) (by simp) with h2020 | h2020
                            · linarith only [h1985, h2020, hlam]
                            · linarith only [h1993, h2020, hlam]
                          · linarith only [h2019, hlam, p1996_0]
                        · linarith only [h2018, h4, hlam]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h2, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h1985, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h1991, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h0, h1985, hc01, hc25, hlam, hphi, ht0b, ht5b, p1996_1]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h3, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h1986, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h0, h1986, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1996_1]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h0, h1986, h1993, h1995, hc01, hc45, hlam, hphi, ht0b, ht5b, p1996_1]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h4, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h1987, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h1993, hlam, p1996_1]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [h1994, hlam, p1996_0]
                      · have p1996_0 := h1996c.1
                        have p1996_1 := h1996c.2.1
                        have p1996_2 := h1996c.2.2.1
                        have p1996_3 := h1996c.2.2.2
                        linarith only [hlam, p1996_0]
                    · linarith only [h1984, h1995, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                  · linarith only [h1991, h1993, h1994, hlam]
                · linarith only [h1984, h1993, h5, hc23, hc34, hlam, hphi]
            · linarith only [h1984, h1990, h5, hc13, hc34, hlam, hphi]
        · linarith only [h1984, h1985, h1987, h4, h5, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2045 | h2045
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2046 | h2046
          · linarith only [h2046, h5, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2048 | h2048
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2049 | h2049
              · linarith only [h1984, h1985, h1986, h2049, h3, h5, hc04, hlam, hphi, u0ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2051 | h2051
                · linarith only [h0, h1985, h1986, h2051, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h1984, h2051, h5, hc23, hc34, hlam, hphi]
            · linarith only [h1984, h2048, h5, hc13, hc34, hlam, hphi]
        · linarith only [h1984, h1985, h2045, h4, h5, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2056 | h2056
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2057 | h2057
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2058 | h2058
          · linarith only [h2058, h5, hc13, hlam, hphi, ht01, u0ehi2]
          · linarith only [h1985, h2056, h2058, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2061 | h2061
          · linarith only [h1984, h2056, h2057, h2061, h4, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h1985, h2056, h2061, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2064 | h2064
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2065 | h2065
          · linarith only [h2065, h5, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2067 | h2067
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2068 | h2068
              · linarith only [h2, h2068, h5, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2070 | h2070
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2071 | h2071
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2072 | h2072
                    · rcases h2bigk with h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c | h2073c
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        rcases p2073_3 (m.d 0 2) (by simp) with h2075 | h2075
                        · rcases p2073_3 (m.d 1 2) (by simp) with h2076 | h2076
                          · linarith only [h0, h2076, hlam]
                          · rcases p2073_3 (m.d 2 3) (by simp) with h2078 | h2078
                            · linarith only [h2, h2078, hlam]
                            · linarith only [h1985, h2078, hlam]
                        · linarith only [h0, h2075, hlam]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h0, h1985, h2064, h2070, h2072, hc01, hc45, hlam, hphi, ht0b, ht5b, p2073_1]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h0, h2056, h2064, h2070, h2072, hc01, hc45, hlam, hphi, ht0b, ht5b, p2073_1]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h1985, h2, h2064, hlam, p2073_2]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h0, hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h1985, hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h2056, hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h1985, h2, h2070, h2072, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2073_1]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h2, hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h2, h5, hc12, hc34, hlam, hphi, ht23, p2073_1]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h2068, hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        rcases p2073_3 (m.d 0 2) (by simp) with h2094 | h2094
                        · rcases p2073_3 (m.d 1 2) (by simp) with h2095 | h2095
                          · linarith only [h1985, h2095, hlam]
                          · linarith only [h2064, h2095, hlam]
                        · linarith only [h2094, h4, hlam]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h3, hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h2064, h2070, h2072, h3, hc02, hc45, hlam, hphi, ht0b, ht5b, p2073_1]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h0, h1985, h2064, h2070, h2072, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p2073_1]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        rcases p2073_3 (m.d 0 2) (by simp) with h2103 | h2103
                        · rcases p2073_3 (m.d 1 2) (by simp) with h2104 | h2104
                          · linarith only [h2056, h2104, hlam]
                          · linarith only [h2064, h2104, hlam]
                        · linarith only [h2103, h4, hlam]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h4, hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h2064, hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h2070, hlam, p2073_1]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [h2071, hlam, p2073_0]
                      · have p2073_0 := h2073c.1
                        have p2073_1 := h2073c.2.1
                        have p2073_2 := h2073c.2.2.1
                        have p2073_3 := h2073c.2.2.2
                        linarith only [hlam, p2073_0]
                    · linarith only [h2072, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                  · linarith only [h1985, h2064, h2068, h2071, hlam]
                · linarith only [h1984, h1985, h2064, h2070, hc03, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h1984, h2067, h5, hc13, hc34, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2117 | h2117
          · linarith only [h2117, h5, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2119 | h2119
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2120 | h2120
              · linarith only [h1984, h2, h2120, h5, hc02, hlam, hphi, u0ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2122 | h2122
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2123 | h2123
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2124 | h2124
                    · rcases h2bigk with h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        rcases p2125_3 (m.d 0 2) (by simp) with h2127 | h2127
                        · rcases p2125_3 (m.d 1 2) (by simp) with h2128 | h2128
                          · linarith only [h0, h2128, hlam]
                          · rcases p2125_3 (m.d 2 3) (by simp) with h2130 | h2130
                            · linarith only [h2, h2130, hlam]
                            · linarith only [h1985, h2130, hlam]
                        · linarith only [h0, h2127, hlam]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        rcases p2125_3 (m.d 0 2) (by simp) with h2134 | h2134
                        · rcases p2125_3 (m.d 1 2) (by simp) with h2135 | h2135
                          · linarith only [h0, h2135, hlam]
                          · rcases p2125_3 (m.d 2 3) (by simp) with h2137 | h2137
                            · linarith only [h2137, hlam, p2125_0]
                            · rcases p2125_3 (m.d 2 4) (by simp) with h2139 | h2139
                              · linarith only [h2139, h3, hlam]
                              · linarith only [h2120, h2139, hlam]
                        · linarith only [h2134, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        rcases p2125_3 (m.d 0 2) (by simp) with h2143 | h2143
                        · rcases p2125_3 (m.d 1 2) (by simp) with h2144 | h2144
                          · linarith only [h0, h2144, hlam]
                          · rcases p2125_3 (m.d 2 3) (by simp) with h2146 | h2146
                            · linarith only [h2, h2146, hlam]
                            · rcases p2125_3 (m.d 2 4) (by simp) with h2148 | h2148
                              · linarith only [h2148, hlam, p2125_0]
                              · rcases p2125_3 (m.d 2 5) (by simp) with h2150 | h2150
                                · linarith only [h2150, h4, hlam]
                                · rcases h3bigk with h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c | h2152c
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h5, hc13, hc34, hlam, hphi, p2152_1]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h2064, h2122, h5, hc12, hc34, hlam, hphi, ht23, p2152_1]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h5, hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h2124, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2152_1]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h1, hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h1985, hlam, p2152_1]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h2117, hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h1, h2124, hc01, hc45, hlam, hphi, ht0b, ht5b, p2152_1]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h2, hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h0, h2120, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2125_1, p2152_1]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h2120, hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h0, h2120, h2124, hc01, hc45, hlam, hphi, ht0b, ht5b, p2125_1, p2152_1]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [hc03, hc34, hlam, hphi, p2152_1]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h0, h2064, h2119, h2120, h2122, h2124, hc01, hc12, hc34, hc45, hlam, hphi, ht0b, ht23, ht5b, p2125_1, p2152_1]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h2064, h2122, hc12, hc34, hlam, hphi, ht23, p2152_1]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    rcases p2152_3 (m.d 0 3) (by simp) with h2172 | h2172
                                    · linarith only [h2172, h5, hlam]
                                    · linarith only [h1984, h2172, hlam]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h1984, hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h2119, hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h2122, hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [h2124, hlam, p2152_0]
                                  · have p2152_0 := h2152c.1
                                    have p2152_1 := h2152c.2.1
                                    have p2152_2 := h2152c.2.2.1
                                    have p2152_3 := h2152c.2.2.2
                                    linarith only [hlam, p2152_0]
                        · linarith only [h2143, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        rcases p2125_3 (m.d 0 2) (by simp) with h2181 | h2181
                        · rcases p2125_3 (m.d 1 2) (by simp) with h2182 | h2182
                          · linarith only [h0, h2182, hlam]
                          · rcases p2125_3 (m.d 2 3) (by simp) with h2184 | h2184
                            · linarith only [h2, h2184, hlam]
                            · linarith only [h2122, h2184, hlam]
                        · linarith only [h2181, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h0, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h1985, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2056, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2064, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2, h5, hc12, hc34, hlam, hphi, ht23, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2120, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2, h2064, h5, hc12, hc34, hlam, hphi, ht23, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h3, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        rcases p2125_3 (m.d 0 2) (by simp) with h2199 | h2199
                        · rcases p2125_3 (m.d 1 2) (by simp) with h2200 | h2200
                          · linarith only [h2200, hlam, p2125_0]
                          · rcases p2125_3 (m.d 2 3) (by simp) with h2202 | h2202
                            · linarith only [h2120, h2202, hlam]
                            · linarith only [h1985, h2202, hlam]
                        · linarith only [h0, h2199, hlam]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h1985, hc12, hc24, hlam, hphi, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h0, h2064, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h4, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2, h2122, h5, hc12, hc34, hlam, hphi, ht23, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2122, hlam, p2125_1]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [h2123, hlam, p2125_0]
                      · have p2125_0 := h2125c.1
                        have p2125_1 := h2125c.2.1
                        have p2125_2 := h2125c.2.2.1
                        have p2125_3 := h2125c.2.2.2
                        linarith only [hlam, p2125_0]
                    · linarith only [h2124, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                  · linarith only [h2120, h2122, h2123, hlam]
                · linarith only [h1, h2119, h2122, h5, hc23, hc34, hlam, hphi]
            · linarith only [h1984, h2119, h5, hc13, hc34, hlam, hphi]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2218 | h2218
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2219 | h2219
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2220 | h2220
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2221 | h2221
          · linarith only [h2221, h5, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2223 | h2223
            · linarith only [h1984, h2219, h2221, h2223, hc12, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2225 | h2225
              · linarith only [h2225, h5, hc23, hlam, hphi, ht01, ht12, u0ehi2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2227 | h2227
                · linarith only [h1984, h2218, h2227, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2229 | h2229
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2230 | h2230
                    · rcases h2bigk with h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, h2219, h2229, hc01, hc45, hlam, hphi, ht0b, ht5b, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        rcases p2231_3 (m.d 0 2) (by simp) with h2234 | h2234
                        · rcases p2231_3 (m.d 1 2) (by simp) with h2235 | h2235
                          · linarith only [h0, h2235, hlam]
                          · linarith only [h2218, h2235, hlam]
                        · linarith only [h2234, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        rcases p2231_3 (m.d 0 2) (by simp) with h2239 | h2239
                        · rcases p2231_3 (m.d 1 2) (by simp) with h2240 | h2240
                          · linarith only [h0, h2240, hlam]
                          · linarith only [h2219, h2240, hlam]
                        · linarith only [h2239, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        rcases p2231_3 (m.d 0 2) (by simp) with h2244 | h2244
                        · rcases p2231_3 (m.d 1 2) (by simp) with h2245 | h2245
                          · linarith only [h0, h2245, hlam]
                          · linarith only [h2220, h2245, hlam]
                        · linarith only [h2244, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        rcases p2231_3 (m.d 0 2) (by simp) with h2251 | h2251
                        · rcases p2231_3 (m.d 1 2) (by simp) with h2252 | h2252
                          · rcases p2231_3 (m.d 2 3) (by simp) with h2253 | h2253
                            · linarith only [h2253, hlam, p2231_0]
                            · rcases p2231_3 (m.d 2 4) (by simp) with h2255 | h2255
                              · linarith only [h2219, h2255, hlam]
                              · linarith only [h2225, h2255, hlam]
                          · linarith only [h2252, hlam, p2231_0]
                        · linarith only [h2, h2251, hlam]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, h2229, hc01, hc45, hlam, hphi, ht0b, ht5b, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        rcases p2231_3 (m.d 0 2) (by simp) with h2261 | h2261
                        · rcases p2231_3 (m.d 1 2) (by simp) with h2262 | h2262
                          · rcases p2231_3 (m.d 2 3) (by simp) with h2263 | h2263
                            · linarith only [h2218, h2263, hlam]
                            · rcases p2231_3 (m.d 2 4) (by simp) with h2265 | h2265
                              · linarith only [h2219, h2265, hlam]
                              · linarith only [h2229, h2265, hlam]
                          · linarith only [h2262, hlam, p2231_0]
                        · linarith only [h2261, h4, hlam]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2218, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2225, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2227, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h3, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2219, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, h2219, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, h2219, hc01, hc25, hlam, hphi, ht0b, ht5b, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h4, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2220, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h0, h2220, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2231_1]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [h2229, hlam, p2231_0]
                      · have p2231_0 := h2231c.1
                        have p2231_1 := h2231c.2.1
                        have p2231_2 := h2231c.2.2.1
                        have p2231_3 := h2231c.2.2.2
                        linarith only [hlam, p2231_0]
                    · linarith only [h2230, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2286 | h2286
                    · rcases h2bigk with h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c | h2287c
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        rcases p2287_3 (m.d 0 2) (by simp) with h2289 | h2289
                        · rcases p2287_3 (m.d 1 2) (by simp) with h2290 | h2290
                          · linarith only [h0, h2290, hlam]
                          · rcases p2287_3 (m.d 2 3) (by simp) with h2292 | h2292
                            · linarith only [h2, h2292, hlam]
                            · rcases p2287_3 (m.d 2 4) (by simp) with h2294 | h2294
                              · linarith only [h2294, h3, hlam]
                              · rcases p2287_3 (m.d 2 5) (by simp) with h2296 | h2296
                                · linarith only [h2296, h4, hlam]
                                · rcases h3bigk with h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c | h2298c
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h1984, h2286, hc13, hc34, hlam, hphi, p2298_1]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h1984, h2286, hc23, hc34, hlam, hphi, p2298_1]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h5, hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h1984, hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h1, hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2298_1]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h2221, hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h2223, hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h2, hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h2218, hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h2225, hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h2227, hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [hc03, hc34, hlam, hphi, p2298_1]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h2218, hc23, hc34, hlam, hphi, p2298_1]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [hc23, hc34, hlam, hphi, p2298_1]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h1984, hc34, hlam, hphi, ht01, ht12, ht23, p2298_1, u0ehi2]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p2298_1, u0ehi2]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h2218, hc23, hc35, hlam, hphi, p2298_1]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [hc23, hc35, hlam, hphi, p2298_1]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [h2286, hlam, p2298_0]
                                  · have p2298_0 := h2298c.1
                                    have p2298_1 := h2298c.2.1
                                    have p2298_2 := h2298c.2.2.1
                                    have p2298_3 := h2298c.2.2.2
                                    linarith only [hlam, p2298_0]
                        · linarith only [h0, h2289, hlam]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        rcases p2287_3 (m.d 0 2) (by simp) with h2325 | h2325
                        · rcases p2287_3 (m.d 1 2) (by simp) with h2326 | h2326
                          · linarith only [h0, h2326, hlam]
                          · linarith only [h2218, h2326, hlam]
                        · linarith only [h2325, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        rcases p2287_3 (m.d 0 2) (by simp) with h2330 | h2330
                        · rcases p2287_3 (m.d 1 2) (by simp) with h2331 | h2331
                          · linarith only [h0, h2331, hlam]
                          · linarith only [h2219, h2331, hlam]
                        · linarith only [h2330, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        rcases p2287_3 (m.d 0 2) (by simp) with h2335 | h2335
                        · rcases p2287_3 (m.d 1 2) (by simp) with h2336 | h2336
                          · linarith only [h0, h2336, hlam]
                          · linarith only [h2220, h2336, hlam]
                        · linarith only [h2335, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h0, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        rcases p2287_3 (m.d 0 2) (by simp) with h2342 | h2342
                        · rcases p2287_3 (m.d 1 2) (by simp) with h2343 | h2343
                          · rcases p2287_3 (m.d 2 3) (by simp) with h2344 | h2344
                            · linarith only [h2344, hlam, p2287_0]
                            · rcases p2287_3 (m.d 2 4) (by simp) with h2346 | h2346
                              · linarith only [h2219, h2346, hlam]
                              · linarith only [h2225, h2346, hlam]
                          · linarith only [h2343, hlam, p2287_0]
                        · linarith only [h2, h2342, hlam]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        rcases p2287_3 (m.d 0 2) (by simp) with h2351 | h2351
                        · rcases p2287_3 (m.d 1 2) (by simp) with h2352 | h2352
                          · rcases p2287_3 (m.d 2 3) (by simp) with h2353 | h2353
                            · linarith only [h2218, h2353, hlam]
                            · rcases p2287_3 (m.d 2 4) (by simp) with h2355 | h2355
                              · linarith only [h2355, hlam, p2287_0]
                              · rcases p2287_3 (m.d 2 5) (by simp) with h2357 | h2357
                                · linarith only [h2220, h2357, hlam]
                                · linarith only [h2229, h2357, hlam]
                          · linarith only [h2352, hlam, p2287_0]
                        · linarith only [h2351, h3, hlam]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        rcases p2287_3 (m.d 0 2) (by simp) with h2362 | h2362
                        · rcases p2287_3 (m.d 1 2) (by simp) with h2363 | h2363
                          · rcases p2287_3 (m.d 2 3) (by simp) with h2364 | h2364
                            · linarith only [h2218, h2364, hlam]
                            · rcases p2287_3 (m.d 2 4) (by simp) with h2366 | h2366
                              · linarith only [h2219, h2366, hlam]
                              · rcases p2287_3 (m.d 2 5) (by simp) with h2368 | h2368
                                · linarith only [h2368, hlam, p2287_0]
                                · rcases h3bigk with h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h2218, h5, hc23, hc34, hlam, hphi, p2370_1]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h5, hc23, hc34, hlam, hphi, p2370_1]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h5, hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h1984, hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h1, hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2370_1]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h2221, hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h2223, hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h2, hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h2218, hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h2225, hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h2227, hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [hc03, hc34, hlam, hphi, p2370_1]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [hc13, hc34, hlam, hphi, p2370_1]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [hc23, hc34, hlam, hphi, p2370_1]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h1984, hc34, hlam, hphi, ht01, ht12, ht23, p2370_1, u0ehi4]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p2370_1, u0ehi2]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h2218, hc23, hc35, hlam, hphi, p2370_1]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [hc23, hc35, hlam, hphi, p2370_1]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [h2286, hlam, p2370_0]
                                  · have p2370_0 := h2370c.1
                                    have p2370_1 := h2370c.2.1
                                    have p2370_2 := h2370c.2.2.1
                                    have p2370_3 := h2370c.2.2.2
                                    linarith only [hlam, p2370_0]
                          · linarith only [h2363, hlam, p2287_0]
                        · linarith only [h2362, h4, hlam]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h2, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h2218, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h2225, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h2227, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h3, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h2219, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h0, h2219, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2287_1]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h2229, hlam, p2287_1]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h4, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h2220, hlam, p2287_0]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h0, h2220, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2287_1]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [h0, h2220, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2287_1]
                      · have p2287_0 := h2287c.1
                        have p2287_1 := h2287c.2.1
                        have p2287_2 := h2287c.2.2.1
                        have p2287_3 := h2287c.2.2.2
                        linarith only [hlam, p2287_0]
                    · linarith only [h2286, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2414 | h2414
          · linarith only [h2414, h5, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2416 | h2416
            · linarith only [h0, h1984, h2219, h2220, h2414, h2416, h4, hc01, hlam, hphi, u0ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2418 | h2418
              · linarith only [h2418, h5, hc23, hlam, hphi, ht01, ht12, u0ehi2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2420 | h2420
                · linarith only [h1984, h2420, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2422 | h2422
                  · linarith only [h0, h2219, h2220, h2422, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2424 | h2424
                    · linarith only [h2219, h2220, h2418, h2422, h2424, hc23, hc34, hlam, hphi]
                    · linarith only [h2424, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2427 | h2427
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2428 | h2428
          · linarith only [h2428, h5, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2430 | h2430
            · linarith only [h1984, h2218, h2219, h2430, h3, hc04, hlam, hphi, u0ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2432 | h2432
              · linarith only [h0, h2, h2432, h5, hc01, hlam, hphi, u0ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2434 | h2434
                · linarith only [h0, h1984, h2218, h2219, h2434, h3, hc01, hlam, hphi, u0ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2436 | h2436
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2437 | h2437
                    · rcases h2bigk with h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        rcases p2438_3 (m.d 0 2) (by simp) with h2440 | h2440
                        · rcases p2438_3 (m.d 1 2) (by simp) with h2441 | h2441
                          · linarith only [h0, h2441, hlam]
                          · rcases p2438_3 (m.d 2 3) (by simp) with h2443 | h2443
                            · linarith only [h2, h2443, hlam]
                            · rcases p2438_3 (m.d 2 4) (by simp) with h2445 | h2445
                              · linarith only [h2445, h3, hlam]
                              · linarith only [h2219, h2445, hlam]
                        · linarith only [h0, h2440, hlam]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h2219, h2427, h2434, h3, hlam, p2438_2]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h0, h2219, h2427, h2434, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2438_1]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h2219, h2427, h3, hlam, p2438_2]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h0, hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h2219, h3, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2438_1]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h2219, hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h0, h2219, h2434, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2438_1]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h2, hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h2218, hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h2432, hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h2434, hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h3, hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h0, h2218, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2438_1]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        rcases p2438_3 (m.d 0 2) (by simp) with h2464 | h2464
                        · rcases p2438_3 (m.d 1 2) (by simp) with h2465 | h2465
                          · linarith only [h2219, h2465, hlam]
                          · linarith only [h2218, h2465, hlam]
                        · linarith only [h2, h2464, hlam]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        rcases p2438_3 (m.d 0 2) (by simp) with h2470 | h2470
                        · rcases p2438_3 (m.d 1 2) (by simp) with h2471 | h2471
                          · linarith only [h2219, h2471, hlam]
                          · linarith only [h2427, h2471, hlam]
                        · linarith only [h2470, h4, hlam]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h4, hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h2427, hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h0, h2427, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2438_1]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [h2436, hlam, p2438_0]
                      · have p2438_0 := h2438c.1
                        have p2438_1 := h2438c.2.1
                        have p2438_2 := h2438c.2.2.1
                        have p2438_3 := h2438c.2.2.2
                        linarith only [hlam, p2438_0]
                    · linarith only [h0, h2219, h2427, h2436, h2437, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h2218, h2219, h2436, hc23, hc45, hlam, hphi, ht34]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2482 | h2482
          · linarith only [h2482, h5, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2484 | h2484
            · linarith only [h1984, h2218, h2219, h2484, h3, hc04, hlam, hphi, u0ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2486 | h2486
              · linarith only [h0, h2218, h2219, h2486, h3, h5, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2488 | h2488
                · linarith only [h0, h1984, h2218, h2219, h2488, h3, hc01, hlam, hphi, u0ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2490 | h2490
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2491 | h2491
                    · rcases h2bigk with h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        rcases p2492_3 (m.d 0 2) (by simp) with h2494 | h2494
                        · rcases p2492_3 (m.d 1 2) (by simp) with h2495 | h2495
                          · linarith only [h0, h2495, hlam]
                          · rcases p2492_3 (m.d 2 3) (by simp) with h2497 | h2497
                            · linarith only [h2, h2497, hlam]
                            · rcases p2492_3 (m.d 2 4) (by simp) with h2499 | h2499
                              · linarith only [h2499, h3, hlam]
                              · linarith only [h2219, h2499, hlam]
                        · linarith only [h0, h2494, hlam]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h2218, h2427, h2490, h3, hlam, p2492_2]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h0, h2218, h2427, h2490, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2492_1]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h0, h2218, h2427, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2492_1]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h0, hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h0, h2427, h2490, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2492_1]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h2219, hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h2427, hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h2, hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h2218, hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h2486, hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h2488, hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h3, hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h0, h2218, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2492_1]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        rcases p2492_3 (m.d 0 2) (by simp) with h2518 | h2518
                        · rcases p2492_3 (m.d 1 2) (by simp) with h2519 | h2519
                          · linarith only [h2219, h2519, hlam]
                          · linarith only [h2218, h2519, hlam]
                        · linarith only [h2, h2518, hlam]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h0, h2218, h2427, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2492_1]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h4, hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h0, h2218, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2492_1]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        rcases p2492_3 (m.d 0 2) (by simp) with h2527 | h2527
                        · rcases p2492_3 (m.d 1 2) (by simp) with h2528 | h2528
                          · linarith only [h2427, h2528, hlam]
                          · linarith only [h2218, h2528, hlam]
                        · linarith only [h2, h2527, hlam]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [h2490, hlam, p2492_0]
                      · have p2492_0 := h2492c.1
                        have p2492_1 := h2492c.2.1
                        have p2492_2 := h2492c.2.2.1
                        have p2492_3 := h2492c.2.2.2
                        linarith only [hlam, p2492_0]
                    · linarith only [h0, h2490, h2491, h3, h5, hc01, hlam, hphi, u0ehi2]
                  · linarith only [h2218, h2219, h2490, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2536 | h2536
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2537 | h2537
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2538 | h2538
          · linarith only [h2, h2218, h2536, h2538, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h2218, h2536, h2538, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2541 | h2541
          · linarith only [h2, h2218, h2536, h2541, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h2218, h2536, h2541, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2544 | h2544
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2545 | h2545
          · linarith only [h2, h2218, h2544, h2545, h5, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2547 | h2547
            · linarith only [h1984, h2, h2218, h2547, hlam]
            · linarith only [h2218, h2544, h2547, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2550 | h2550
          · linarith only [h2550, h5, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2552 | h2552
            · linarith only [h1984, h2, h2218, h2552, h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2554 | h2554
              · linarith only [h2, h2554, h5, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2556 | h2556
                · linarith only [h1984, h2, h2556, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2558 | h2558
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2559 | h2559
                    · rcases h2bigk with h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c | h2560c
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        rcases p2560_3 (m.d 0 2) (by simp) with h2562 | h2562
                        · rcases p2560_3 (m.d 1 2) (by simp) with h2563 | h2563
                          · linarith only [h0, h2563, hlam]
                          · rcases p2560_3 (m.d 2 3) (by simp) with h2565 | h2565
                            · linarith only [h2, h2565, hlam]
                            · linarith only [h2218, h2565, hlam]
                        · linarith only [h0, h2562, hlam]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        rcases p2560_3 (m.d 0 2) (by simp) with h2569 | h2569
                        · rcases p2560_3 (m.d 1 2) (by simp) with h2570 | h2570
                          · linarith only [h0, h2570, hlam]
                          · rcases p2560_3 (m.d 2 3) (by simp) with h2572 | h2572
                            · linarith only [h2572, hlam, p2560_0]
                            · rcases p2560_3 (m.d 2 4) (by simp) with h2574 | h2574
                              · linarith only [h2574, h3, hlam]
                              · linarith only [h2554, h2574, hlam]
                        · linarith only [h2569, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        rcases p2560_3 (m.d 0 2) (by simp) with h2578 | h2578
                        · rcases p2560_3 (m.d 1 2) (by simp) with h2579 | h2579
                          · linarith only [h0, h2579, hlam]
                          · rcases p2560_3 (m.d 2 3) (by simp) with h2581 | h2581
                            · linarith only [h2, h2581, hlam]
                            · rcases p2560_3 (m.d 2 4) (by simp) with h2583 | h2583
                              · linarith only [h2583, hlam, p2560_0]
                              · rcases p2560_3 (m.d 2 5) (by simp) with h2585 | h2585
                                · linarith only [h2585, h4, hlam]
                                · rcases h3bigk with h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h1984, h2559, hc13, hc34, hlam, hphi, p2587_1]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h1984, h2218, h2559, hc12, hc34, hlam, hphi, ht23, p2587_1]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h5, hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h1984, hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h1, hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h2218, hlam, p2587_1]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h2550, hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h2552, hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h2, hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h0, h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2587_1]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h2554, hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h2556, hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [hc03, hc34, hlam, hphi, p2587_1]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h2218, hc12, hc34, hlam, hphi, ht23, p2587_1]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h2218, hc12, hc34, hlam, hphi, ht23, p2587_1]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h1984, hc34, hlam, hphi, ht01, ht12, ht23, p2587_1, u0ehi2]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p2587_1, u0ehi2]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h2218, hc12, hc35, hlam, hphi, ht23, p2587_1]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h2218, hc12, hc35, hlam, hphi, ht23, p2587_1]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [h2559, hlam, p2587_0]
                                  · have p2587_0 := h2587c.1
                                    have p2587_1 := h2587c.2.1
                                    have p2587_2 := h2587c.2.2.1
                                    have p2587_3 := h2587c.2.2.2
                                    linarith only [hlam, p2587_0]
                        · linarith only [h2578, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        rcases p2560_3 (m.d 0 2) (by simp) with h2614 | h2614
                        · rcases p2560_3 (m.d 1 2) (by simp) with h2615 | h2615
                          · linarith only [h0, h2615, hlam]
                          · rcases p2560_3 (m.d 2 3) (by simp) with h2617 | h2617
                            · linarith only [h2, h2617, hlam]
                            · rcases p2560_3 (m.d 2 4) (by simp) with h2619 | h2619
                              · linarith only [h2619, h3, hlam]
                              · linarith only [h2558, h2619, hlam]
                        · linarith only [h2614, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h0, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h2218, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h2536, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h2544, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h2, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h2, h5, hc12, hc34, hlam, hphi, ht23, p2560_1]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h2554, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h2556, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h3, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        rcases p2560_3 (m.d 0 2) (by simp) with h2634 | h2634
                        · rcases p2560_3 (m.d 1 2) (by simp) with h2635 | h2635
                          · linarith only [h2635, hlam, p2560_0]
                          · rcases p2560_3 (m.d 2 3) (by simp) with h2637 | h2637
                            · linarith only [h2554, h2637, hlam]
                            · linarith only [h2218, h2637, hlam]
                        · linarith only [h0, h2634, hlam]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h0, h2218, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2560_1]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h0, h2218, h2556, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2560_1]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h4, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        rcases p2560_3 (m.d 0 2) (by simp) with h2645 | h2645
                        · rcases p2560_3 (m.d 1 2) (by simp) with h2646 | h2646
                          · linarith only [h2646, hlam, p2560_0]
                          · rcases p2560_3 (m.d 2 3) (by simp) with h2648 | h2648
                            · linarith only [h2556, h2648, hlam]
                            · linarith only [h2218, h2648, hlam]
                        · linarith only [h0, h2645, hlam]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h2218, hc12, hc25, hlam, hphi, p2560_1]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [h2558, hlam, p2560_0]
                      · have p2560_0 := h2560c.1
                        have p2560_1 := h2560c.2.1
                        have p2560_2 := h2560c.2.2.1
                        have p2560_3 := h2560c.2.2.2
                        linarith only [hlam, p2560_0]
                    · linarith only [h0, h2558, h2559, h3, h5, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2656 | h2656
                    · linarith only [h2536, h2558, h2656, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h2656, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]

set_option maxHeartbeats 5308000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s4 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5

set_option maxHeartbeats 5392000 in
set_option maxHeartbeats 5392000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s3 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_23_L_R_L_I_H_I_s4 m hb0 hb2 hb3 h0 h1 h2 h3 h4
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2659 | h2659
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2660 | h2660
      · linarith only [h2, h2660, h4, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2662 | h2662
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2663 | h2663
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2664 | h2664
            · linarith only [h2, h2659, h2664, h4, hc12, hlam, hphi, ht01, u0ehi3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2666 | h2666
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2667 | h2667
                · linarith only [h2659, h2660, h2667, hc13, hlam, hphi, ht01, u0ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2669 | h2669
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2670 | h2670
                    · linarith only [h0, h2659, h2660, h2662, h2670, hc02, hlam, hphi, u0ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2672 | h2672
                      · linarith only [h0, h2662, h2669, h2672, h4, hlam]
                      · linarith only [h0, h2662, h2669, h2672, h4, hc34, hc45, hlam, hphi]
                  · linarith only [h2659, h2660, h2669, hc23, hc35, hlam, hphi]
              · linarith only [h2659, h2660, h2666, hc13, hc35, hlam, hphi]
          · linarith only [h2663, h3, h4, hc12, hc25, hlam, hphi]
        · linarith only [h2, h2662, h4, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2679 | h2679
      · linarith only [h2659, h2679, h3, h4, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2681 | h2681
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2682 | h2682
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2683 | h2683
            · linarith only [h0, h2683, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2685 | h2685
              · linarith only [h2659, h2685, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2687 | h2687
                · linarith only [h1, h2679, h2687, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2689 | h2689
                  · linarith only [h0, h2659, h2681, h2689, h4, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2691 | h2691
                    · linarith only [h0, h2679, h2682, h2689, h2691, h4, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2693 | h2693
                      · linarith only [h0, h2682, h2693, h4, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2695 | h2695
                        · linarith only [h0, h2682, h2689, h2693, h2695, h4, hc23, hc34, hlam, hphi]
                        · linarith only [h2659, h2695, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
          · linarith only [h2682, h3, h4, hc12, hc25, hlam, hphi]
        · linarith only [h2, h2681, h4, hc12, hc25, hlam, hphi]

end R2N4
