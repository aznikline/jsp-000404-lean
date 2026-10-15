import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_46S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 3 (by decide) (by decide) with h1961 | h1961
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1962 | h1962
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1963 | h1963
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1964 | h1964
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1965 | h1965
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1966 | h1966
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1967 | h1967
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1968 | h1968
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1969 | h1969
                  · linarith only [h1969, h557, h561, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1971 | h1971
                    · linarith only [h1967, h1971, h556, h557, h561, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
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
                        linarith only [h0, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h451, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h451, h557, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u2ehi3]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, h557, h561, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u2ehi3]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        rcases p1973_3 (m.d 0 1) (by simp) with h1979 | h1979
                        · linarith only [h0, h1979, hlam]
                        · rcases p1973_3 (m.d 0 2) (by simp) with h1981 | h1981
                          · rcases p1973_3 (m.d 0 3) (by simp) with h1982 | h1982
                            · linarith only [h1982, h556, hlam]
                            · linarith only [h1982, h451, hlam]
                          · linarith only [h0, h1981, hlam]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, h559, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1973_1, u3ehi3]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        rcases p1973_3 (m.d 0 1) (by simp) with h1988 | h1988
                        · linarith only [h0, h1988, hlam]
                        · rcases p1973_3 (m.d 0 2) (by simp) with h1990 | h1990
                          · rcases p1973_3 (m.d 0 3) (by simp) with h1991 | h1991
                            · linarith only [h1991, h556, hlam]
                            · linarith only [h1991, h559, hlam]
                          · linarith only [h1990, h557, hlam]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        rcases p1973_3 (m.d 0 1) (by simp) with h1995 | h1995
                        · linarith only [h0, h1995, hlam]
                        · rcases p1973_3 (m.d 0 2) (by simp) with h1997 | h1997
                          · rcases p1973_3 (m.d 0 3) (by simp) with h1998 | h1998
                            · linarith only [h1998, h556, hlam]
                            · linarith only [h1998, h560, hlam]
                          · linarith only [h1997, h558, hlam]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        rcases p1973_3 (m.d 0 1) (by simp) with h2002 | h2002
                        · linarith only [h2002, h451, hlam]
                        · rcases p1973_3 (m.d 0 2) (by simp) with h2004 | h2004
                          · rcases p1973_3 (m.d 0 3) (by simp) with h2005 | h2005
                            · rcases p1973_3 (m.d 0 4) (by simp) with h2006 | h2006
                              · linarith only [h2006, h559, hlam]
                              · rcases p1973_3 (m.d 0 5) (by simp) with h2008 | h2008
                                · linarith only [h2008, h560, hlam]
                                · rcases h0emin with h2010 | h2010 | h2010 | h2010 | h2010
                                  · linarith only [h2010, hc03, hlam, p1973_1]
                                  · rcases h3bigk with h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h451, hlam, p2012_1]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h1961, h1968, h1971, h451, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2012_1, u3ehi3]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      rcases p2012_3 (m.d 0 3) (by simp) with h2016 | h2016
                                      · rcases p2012_3 (m.d 1 3) (by simp) with h2017 | h2017
                                        · rcases p2012_3 (m.d 2 3) (by simp) with h2018 | h2018
                                          · linarith only [h2018, h556, hlam]
                                          · linarith only [h1967, h2018, hlam]
                                        · linarith only [h1964, h2017, hlam]
                                      · linarith only [h2016, hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      rcases p2012_3 (m.d 0 3) (by simp) with h2023 | h2023
                                      · rcases p2012_3 (m.d 1 3) (by simp) with h2024 | h2024
                                        · rcases p2012_3 (m.d 2 3) (by simp) with h2025 | h2025
                                          · linarith only [h2025, h556, hlam]
                                          · linarith only [h1968, h2025, hlam]
                                        · linarith only [h1965, h2024, hlam]
                                      · linarith only [h2023, hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h1961, hc01, hc12, hlam, hphi, p1973_1, p2012_1]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h1961, h1968, h1971, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2012_1, u3ehi3]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      rcases p2012_3 (m.d 0 3) (by simp) with h2033 | h2033
                                      · linarith only [h2033, h451, hlam]
                                      · linarith only [h2033, h559, hlam]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      rcases p2012_3 (m.d 0 3) (by simp) with h2036 | h2036
                                      · linarith only [h2036, h451, hlam]
                                      · linarith only [h2036, h560, hlam]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h556, hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h1961, hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2012_1, u3ehi3]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h0, h1971, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2012_1, u3ehi3]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h559, hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h1964, hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h1967, hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h1971, hlam, p2012_1]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h560, hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h1965, hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [h1968, hlam, p2012_0]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [hc35, hlam, hphi, p2012_1, u3ehi3]
                                    · have p2012_0 := h2012c.1
                                      have p2012_1 := h2012c.2.1
                                      have p2012_2 := h2012c.2.2.1
                                      have p2012_3 := h2012c.2.2.2
                                      linarith only [hlam, p2012_0]
                                  · rcases h3bigk with h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h451, hlam, p2054_1]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h1961, h1967, h451, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2054_1, u3ehi3]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      rcases p2054_3 (m.d 0 3) (by simp) with h2058 | h2058
                                      · rcases p2054_3 (m.d 1 3) (by simp) with h2059 | h2059
                                        · rcases p2054_3 (m.d 2 3) (by simp) with h2060 | h2060
                                          · linarith only [h2060, h556, hlam]
                                          · linarith only [h1967, h2060, hlam]
                                        · linarith only [h1964, h2059, hlam]
                                      · linarith only [h2058, hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      rcases p2054_3 (m.d 0 3) (by simp) with h2065 | h2065
                                      · rcases p2054_3 (m.d 1 3) (by simp) with h2066 | h2066
                                        · rcases p2054_3 (m.d 2 3) (by simp) with h2067 | h2067
                                          · linarith only [h2067, h556, hlam]
                                          · linarith only [h1968, h2067, hlam]
                                        · linarith only [h1965, h2066, hlam]
                                      · linarith only [h2065, hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h1961, h2010, hc12, hlam, ht01, p2054_1]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h1961, h1968, h1971, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2054_1, u3ehi3]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      rcases p2054_3 (m.d 0 3) (by simp) with h2075 | h2075
                                      · linarith only [h2075, h451, hlam]
                                      · linarith only [h2075, h559, hlam]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      rcases p2054_3 (m.d 0 3) (by simp) with h2078 | h2078
                                      · linarith only [h2078, h451, hlam]
                                      · linarith only [h2078, h560, hlam]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h556, hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h1961, hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2054_1, u3ehi3]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h0, h1971, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2054_1, u3ehi3]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h559, hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h1964, hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h1967, hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h1971, hlam, p2054_1]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h560, hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h1965, hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [h1968, hlam, p2054_0]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [hc35, hlam, hphi, p2054_1, u3ehi3]
                                    · have p2054_0 := h2054c.1
                                      have p2054_1 := h2054c.2.1
                                      have p2054_2 := h2054c.2.2.1
                                      have p2054_3 := h2054c.2.2.2
                                      linarith only [hlam, p2054_0]
                                  · linarith only [h2008, h2010, h561, hc03, hlam, p1973_1]
                                  · linarith only [h2008, h2010, hc03, hlam, p1973_1]
                            · linarith only [h2005, h451, hlam]
                          · linarith only [h0, h2004, hlam]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h556, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        rcases p1973_3 (m.d 0 1) (by simp) with h2102 | h2102
                        · linarith only [h2102, h451, hlam]
                        · rcases p1973_3 (m.d 0 2) (by simp) with h2104 | h2104
                          · rcases p1973_3 (m.d 0 3) (by simp) with h2105 | h2105
                            · rcases p1973_3 (m.d 0 4) (by simp) with h2106 | h2106
                              · linarith only [h2106, h559, hlam]
                              · rcases p1973_3 (m.d 0 5) (by simp) with h2108 | h2108
                                · linarith only [h2108, h560, hlam]
                                · linarith only [h2108, h561, hlam]
                            · linarith only [h2105, h559, hlam]
                          · linarith only [h2104, h557, hlam]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        rcases p1973_3 (m.d 0 1) (by simp) with h2113 | h2113
                        · linarith only [h2113, h451, hlam]
                        · rcases p1973_3 (m.d 0 2) (by simp) with h2115 | h2115
                          · rcases p1973_3 (m.d 0 3) (by simp) with h2116 | h2116
                            · rcases p1973_3 (m.d 0 4) (by simp) with h2117 | h2117
                              · linarith only [h2117, h559, hlam]
                              · rcases p1973_3 (m.d 0 5) (by simp) with h2119 | h2119
                                · linarith only [h2119, h560, hlam]
                                · rcases h0emin with h2121 | h2121 | h2121 | h2121 | h2121
                                  · linarith only [h0, h2121, hc12, hlam, ht01]
                                  · rcases h3bigk with h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [hlam, p2123_0]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h451, hlam, p2123_1]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h1961, h1967, h451, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2123_1, u3ehi3]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      rcases p2123_3 (m.d 0 3) (by simp) with h2127 | h2127
                                      · rcases p2123_3 (m.d 1 3) (by simp) with h2128 | h2128
                                        · rcases p2123_3 (m.d 2 3) (by simp) with h2129 | h2129
                                          · linarith only [h2129, h556, hlam]
                                          · linarith only [h1967, h2129, hlam]
                                        · linarith only [h1964, h2128, hlam]
                                      · linarith only [h2127, hlam, p2123_0]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      rcases p2123_3 (m.d 0 3) (by simp) with h2134 | h2134
                                      · rcases p2123_3 (m.d 1 3) (by simp) with h2135 | h2135
                                        · rcases p2123_3 (m.d 2 3) (by simp) with h2136 | h2136
                                          · linarith only [h2136, h556, hlam]
                                          · linarith only [h1968, h2136, hlam]
                                        · linarith only [h1965, h2135, hlam]
                                      · linarith only [h2134, hlam, p2123_0]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h1961, h1969, h558, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1973_1, p2123_1, u2ehi3]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [hlam, p2123_0]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h1961, h1968, h1971, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2123_1, u3ehi3]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      rcases p2123_3 (m.d 0 3) (by simp) with h2144 | h2144
                                      · linarith only [h2144, h451, hlam]
                                      · linarith only [h2144, h559, hlam]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      rcases p2123_3 (m.d 0 3) (by simp) with h2147 | h2147
                                      · linarith only [h2147, h451, hlam]
                                      · linarith only [h2147, h560, hlam]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h556, hlam, p2123_0]
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
                                      linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2123_1, u3ehi3]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h0, h1971, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2123_1, u3ehi3]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h559, hlam, p2123_0]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h1964, hlam, p2123_0]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h1967, hlam, p2123_0]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [hlam, p2123_0]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h1971, hlam, p2123_1]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h560, hlam, p2123_0]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h1965, hlam, p2123_0]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [h1968, hlam, p2123_0]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [hc35, hlam, hphi, p2123_1, u3ehi3]
                                    · have p2123_0 := h2123c.1
                                      have p2123_1 := h2123c.2.1
                                      have p2123_2 := h2123c.2.2.1
                                      have p2123_3 := h2123c.2.2.2
                                      linarith only [hlam, p2123_0]
                                  · rcases h3bigk with h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c | h2165c
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h451, hlam, p2165_1]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h1961, h1967, h451, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2165_1, u3ehi3]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      rcases p2165_3 (m.d 0 3) (by simp) with h2169 | h2169
                                      · rcases p2165_3 (m.d 1 3) (by simp) with h2170 | h2170
                                        · rcases p2165_3 (m.d 2 3) (by simp) with h2171 | h2171
                                          · linarith only [h2171, h556, hlam]
                                          · linarith only [h1967, h2171, hlam]
                                        · linarith only [h1964, h2170, hlam]
                                      · linarith only [h2169, hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      rcases p2165_3 (m.d 0 3) (by simp) with h2176 | h2176
                                      · rcases p2165_3 (m.d 1 3) (by simp) with h2177 | h2177
                                        · rcases p2165_3 (m.d 2 3) (by simp) with h2178 | h2178
                                          · linarith only [h2178, h556, hlam]
                                          · linarith only [h1968, h2178, hlam]
                                        · linarith only [h1965, h2177, hlam]
                                      · linarith only [h2176, hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h1961, h2121, hc12, hlam, ht01, p2165_1]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h1961, h1968, h1971, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2165_1, u3ehi3]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      rcases p2165_3 (m.d 0 3) (by simp) with h2186 | h2186
                                      · linarith only [h2186, h451, hlam]
                                      · linarith only [h2186, h559, hlam]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      rcases p2165_3 (m.d 0 3) (by simp) with h2189 | h2189
                                      · linarith only [h2189, h451, hlam]
                                      · linarith only [h2189, h560, hlam]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h556, hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h1961, hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2165_1, u3ehi3]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h0, h1971, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2165_1, u3ehi3]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h559, hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h1964, hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h1967, hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h1971, hlam, p2165_1]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h560, hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h1965, hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [h1968, hlam, p2165_0]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [hc35, hlam, hphi, p2165_1, u3ehi3]
                                    · have p2165_0 := h2165c.1
                                      have p2165_1 := h2165c.2.1
                                      have p2165_2 := h2165c.2.2.1
                                      have p2165_3 := h2165c.2.2.2
                                      linarith only [hlam, p2165_0]
                                  · linarith only [h1966, h2121, h561, hc14, hlam, ht01]
                                  · linarith only [h2121, hc03, hlam, p1973_1]
                            · linarith only [h2116, h560, hlam]
                          · linarith only [h2115, h558, hlam]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1961, h1964, h1966, h561, hc01, hc12, hlam, hphi, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h557, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h559, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h561, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1961, h1964, h1966, h561, hc01, hc12, hlam, hphi, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h558, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h560, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1961, h1964, h1966, h557, h561, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1973_1, u2ehi3]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                · linarith only [h1961, h1964, h1966, h1967, h1968, h560, h561, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h1961, h1964, h1966, h1967, h559, h561, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2223 | h2223
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2224 | h2224
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2225 | h2225
                  · linarith only [h2225, h557, h561, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2227 | h2227
                    · linarith only [h2223, h2227, h556, h561, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h0bigk with h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [hlam, p2229_0]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h0, hlam, p2229_1]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h451, hlam, p2229_0]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h0, h557, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2229_1, u2ehi3]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h1961, h451, h557, h561, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2229_1, u2ehi3]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        rcases p2229_3 (m.d 0 1) (by simp) with h2235 | h2235
                        · linarith only [h0, h2235, hlam]
                        · rcases p2229_3 (m.d 0 2) (by simp) with h2237 | h2237
                          · rcases p2229_3 (m.d 0 3) (by simp) with h2238 | h2238
                            · linarith only [h2238, h556, hlam]
                            · linarith only [h2238, h451, hlam]
                          · linarith only [h0, h2237, hlam]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [hlam, p2229_0]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h0, h2224, h2227, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2229_1, u3ehi3]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        rcases p2229_3 (m.d 0 1) (by simp) with h2244 | h2244
                        · linarith only [h0, h2244, hlam]
                        · rcases p2229_3 (m.d 0 2) (by simp) with h2246 | h2246
                          · rcases p2229_3 (m.d 0 3) (by simp) with h2247 | h2247
                            · linarith only [h2247, h556, hlam]
                            · linarith only [h2247, h559, hlam]
                          · linarith only [h2246, h557, hlam]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        rcases p2229_3 (m.d 0 1) (by simp) with h2251 | h2251
                        · linarith only [h0, h2251, hlam]
                        · rcases p2229_3 (m.d 0 2) (by simp) with h2253 | h2253
                          · rcases p2229_3 (m.d 0 3) (by simp) with h2254 | h2254
                            · linarith only [h2254, h556, hlam]
                            · linarith only [h2254, h560, hlam]
                          · linarith only [h2253, h558, hlam]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        rcases p2229_3 (m.d 0 1) (by simp) with h2258 | h2258
                        · linarith only [h2258, h451, hlam]
                        · rcases p2229_3 (m.d 0 2) (by simp) with h2260 | h2260
                          · rcases p2229_3 (m.d 0 3) (by simp) with h2261 | h2261
                            · rcases p2229_3 (m.d 0 4) (by simp) with h2262 | h2262
                              · linarith only [h2262, h559, hlam]
                              · rcases p2229_3 (m.d 0 5) (by simp) with h2264 | h2264
                                · linarith only [h2264, h560, hlam]
                                · rcases h0emin with h2266 | h2266 | h2266 | h2266 | h2266
                                  · linarith only [h2266, hc03, hlam, p2229_1]
                                  · rcases h3bigk with h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h451, hlam, p2268_1]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h1961, h2224, h2227, h451, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2268_1, u3ehi3]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      rcases p2268_3 (m.d 0 3) (by simp) with h2272 | h2272
                                      · rcases p2268_3 (m.d 1 3) (by simp) with h2273 | h2273
                                        · rcases p2268_3 (m.d 2 3) (by simp) with h2274 | h2274
                                          · linarith only [h2274, h556, hlam]
                                          · linarith only [h2223, h2274, hlam]
                                        · linarith only [h1964, h2273, hlam]
                                      · linarith only [h2272, hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      rcases p2268_3 (m.d 0 3) (by simp) with h2279 | h2279
                                      · rcases p2268_3 (m.d 1 3) (by simp) with h2280 | h2280
                                        · rcases p2268_3 (m.d 2 3) (by simp) with h2281 | h2281
                                          · linarith only [h2281, h556, hlam]
                                          · linarith only [h2224, h2281, hlam]
                                        · linarith only [h1965, h2280, hlam]
                                      · linarith only [h2279, hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h1961, hc01, hc12, hlam, hphi, p2229_1, p2268_1]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h1961, h2224, h2227, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2268_1, u3ehi3]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      rcases p2268_3 (m.d 0 3) (by simp) with h2289 | h2289
                                      · linarith only [h2289, h451, hlam]
                                      · linarith only [h2289, h559, hlam]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      rcases p2268_3 (m.d 0 3) (by simp) with h2292 | h2292
                                      · linarith only [h2292, h451, hlam]
                                      · linarith only [h2292, h560, hlam]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h556, hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h1961, hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2268_1, u3ehi3]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h0, h2227, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2268_1, u3ehi3]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h559, hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h1964, hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h2223, hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h2227, hlam, p2268_1]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h560, hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h1965, hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [h2224, hlam, p2268_0]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [hc35, hlam, hphi, p2268_1, u3ehi3]
                                    · have p2268_0 := h2268c.1
                                      have p2268_1 := h2268c.2.1
                                      have p2268_2 := h2268c.2.2.1
                                      have p2268_3 := h2268c.2.2.2
                                      linarith only [hlam, p2268_0]
                                  · rcases h3bigk with h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h451, hlam, p2310_1]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h1961, h2223, h451, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2310_1, u3ehi3]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      rcases p2310_3 (m.d 0 3) (by simp) with h2314 | h2314
                                      · rcases p2310_3 (m.d 1 3) (by simp) with h2315 | h2315
                                        · rcases p2310_3 (m.d 2 3) (by simp) with h2316 | h2316
                                          · linarith only [h2316, h556, hlam]
                                          · linarith only [h2223, h2316, hlam]
                                        · linarith only [h1964, h2315, hlam]
                                      · linarith only [h2314, hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      rcases p2310_3 (m.d 0 3) (by simp) with h2321 | h2321
                                      · rcases p2310_3 (m.d 1 3) (by simp) with h2322 | h2322
                                        · rcases p2310_3 (m.d 2 3) (by simp) with h2323 | h2323
                                          · linarith only [h2323, h556, hlam]
                                          · linarith only [h2224, h2323, hlam]
                                        · linarith only [h1965, h2322, hlam]
                                      · linarith only [h2321, hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h1961, h2266, hc12, hlam, ht01, p2310_1]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h1961, h2224, h2227, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2310_1, u3ehi3]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      rcases p2310_3 (m.d 0 3) (by simp) with h2331 | h2331
                                      · linarith only [h2331, h451, hlam]
                                      · linarith only [h2331, h559, hlam]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      rcases p2310_3 (m.d 0 3) (by simp) with h2334 | h2334
                                      · linarith only [h2334, h451, hlam]
                                      · linarith only [h2334, h560, hlam]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h556, hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h1961, hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2310_1, u3ehi3]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h0, h2227, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2310_1, u3ehi3]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h559, hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h1964, hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h2223, hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h2227, hlam, p2310_1]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h560, hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h1965, hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [h2224, hlam, p2310_0]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [hc35, hlam, hphi, p2310_1, u3ehi3]
                                    · have p2310_0 := h2310c.1
                                      have p2310_1 := h2310c.2.1
                                      have p2310_2 := h2310c.2.2.1
                                      have p2310_3 := h2310c.2.2.2
                                      linarith only [hlam, p2310_0]
                                  · linarith only [h2264, h2266, h561, hc03, hlam, p2229_1]
                                  · linarith only [h2264, h2266, hc03, hlam, p2229_1]
                            · linarith only [h2261, h451, hlam]
                          · linarith only [h0, h2260, hlam]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h556, hlam, p2229_1]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [hlam, p2229_0]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        rcases p2229_3 (m.d 0 1) (by simp) with h2358 | h2358
                        · linarith only [h2358, h451, hlam]
                        · rcases p2229_3 (m.d 0 2) (by simp) with h2360 | h2360
                          · rcases p2229_3 (m.d 0 3) (by simp) with h2361 | h2361
                            · rcases p2229_3 (m.d 0 4) (by simp) with h2362 | h2362
                              · linarith only [h2362, h559, hlam]
                              · rcases p2229_3 (m.d 0 5) (by simp) with h2364 | h2364
                                · linarith only [h2364, h560, hlam]
                                · linarith only [h2364, h561, hlam]
                            · linarith only [h2361, h559, hlam]
                          · linarith only [h2360, h557, hlam]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        rcases p2229_3 (m.d 0 1) (by simp) with h2369 | h2369
                        · linarith only [h2369, h451, hlam]
                        · rcases p2229_3 (m.d 0 2) (by simp) with h2371 | h2371
                          · rcases p2229_3 (m.d 0 3) (by simp) with h2372 | h2372
                            · rcases p2229_3 (m.d 0 4) (by simp) with h2373 | h2373
                              · linarith only [h2373, h559, hlam]
                              · rcases p2229_3 (m.d 0 5) (by simp) with h2375 | h2375
                                · linarith only [h2375, h560, hlam]
                                · rcases h0emin with h2377 | h2377 | h2377 | h2377 | h2377
                                  · linarith only [h0, h2377, hc12, hlam, ht01]
                                  · rcases h3bigk with h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h451, hlam, p2379_1]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h1961, h2223, h451, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2379_1, u3ehi3]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      rcases p2379_3 (m.d 0 3) (by simp) with h2383 | h2383
                                      · rcases p2379_3 (m.d 1 3) (by simp) with h2384 | h2384
                                        · rcases p2379_3 (m.d 2 3) (by simp) with h2385 | h2385
                                          · linarith only [h2385, h556, hlam]
                                          · linarith only [h2223, h2385, hlam]
                                        · linarith only [h1964, h2384, hlam]
                                      · linarith only [h2383, hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      rcases p2379_3 (m.d 0 3) (by simp) with h2390 | h2390
                                      · rcases p2379_3 (m.d 1 3) (by simp) with h2391 | h2391
                                        · rcases p2379_3 (m.d 2 3) (by simp) with h2392 | h2392
                                          · linarith only [h2392, h556, hlam]
                                          · linarith only [h2224, h2392, hlam]
                                        · linarith only [h1965, h2391, hlam]
                                      · linarith only [h2390, hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h1961, h557, h561, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2229_1, p2379_1, u2ehi3]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h1961, h2224, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2379_1, u3ehi4]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      rcases p2379_3 (m.d 0 3) (by simp) with h2400 | h2400
                                      · linarith only [h2400, h451, hlam]
                                      · linarith only [h2400, h559, hlam]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      rcases p2379_3 (m.d 0 3) (by simp) with h2403 | h2403
                                      · linarith only [h2403, h451, hlam]
                                      · linarith only [h2403, h560, hlam]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h556, hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h1961, hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2379_1, u3ehi3]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h0, h2227, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2379_1, u3ehi3]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h559, hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h1964, hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h2223, hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h2227, hlam, p2379_1]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h560, hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h1965, hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [h2224, hlam, p2379_0]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [hc35, hlam, hphi, p2379_1, u3ehi3]
                                    · have p2379_0 := h2379c.1
                                      have p2379_1 := h2379c.2.1
                                      have p2379_2 := h2379c.2.2.1
                                      have p2379_3 := h2379c.2.2.2
                                      linarith only [hlam, p2379_0]
                                  · rcases h3bigk with h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c | h2421c
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h451, hlam, p2421_1]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h1961, h2223, h451, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2421_1, u3ehi3]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      rcases p2421_3 (m.d 0 3) (by simp) with h2425 | h2425
                                      · rcases p2421_3 (m.d 1 3) (by simp) with h2426 | h2426
                                        · rcases p2421_3 (m.d 2 3) (by simp) with h2427 | h2427
                                          · linarith only [h2427, h556, hlam]
                                          · linarith only [h2223, h2427, hlam]
                                        · linarith only [h1964, h2426, hlam]
                                      · linarith only [h2425, hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      rcases p2421_3 (m.d 0 3) (by simp) with h2432 | h2432
                                      · rcases p2421_3 (m.d 1 3) (by simp) with h2433 | h2433
                                        · rcases p2421_3 (m.d 2 3) (by simp) with h2434 | h2434
                                          · linarith only [h2434, h556, hlam]
                                          · linarith only [h2224, h2434, hlam]
                                        · linarith only [h1965, h2433, hlam]
                                      · linarith only [h2432, hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h1961, h2377, hc12, hlam, ht01, p2421_1]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h1961, h2224, h2227, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2421_1, u3ehi3]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      rcases p2421_3 (m.d 0 3) (by simp) with h2442 | h2442
                                      · linarith only [h2442, h451, hlam]
                                      · linarith only [h2442, h559, hlam]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      rcases p2421_3 (m.d 0 3) (by simp) with h2445 | h2445
                                      · linarith only [h2445, h451, hlam]
                                      · linarith only [h2445, h560, hlam]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h556, hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h1961, hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2421_1, u3ehi3]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h0, h2227, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2421_1, u3ehi3]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h559, hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h1964, hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h2223, hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h2227, hlam, p2421_1]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h560, hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h1965, hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [h2224, hlam, p2421_0]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [hc35, hlam, hphi, p2421_1, u3ehi3]
                                    · have p2421_0 := h2421c.1
                                      have p2421_1 := h2421c.2.1
                                      have p2421_2 := h2421c.2.2.1
                                      have p2421_3 := h2421c.2.2.2
                                      linarith only [hlam, p2421_0]
                                  · linarith only [h2377, h561, hc03, hlam, p2229_1]
                                  · linarith only [h2377, hc03, hlam, p2229_1]
                            · linarith only [h2372, h560, hlam]
                          · linarith only [h2371, h558, hlam]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h561, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2229_1]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h557, hlam, p2229_0]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h559, hlam, p2229_0]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [hlam, p2229_0]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h561, hlam, p2229_0]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        rcases p2229_3 (m.d 0 1) (by simp) with h2472 | h2472
                        · linarith only [h2472, hlam, p2229_0]
                        · rcases p2229_3 (m.d 0 2) (by simp) with h2474 | h2474
                          · rcases p2229_3 (m.d 0 3) (by simp) with h2475 | h2475
                            · rcases p2229_3 (m.d 0 4) (by simp) with h2476 | h2476
                              · linarith only [h2476, h561, hlam]
                              · linarith only [h2476, h557, h561, hc45, hlam, hphi, ht23, ht34, p2229_1, u2ehi3]
                            · linarith only [h2475, h451, hlam]
                          · linarith only [h0, h2474, hlam]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h558, hlam, p2229_1]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h560, hlam, p2229_0]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [h557, h561, hc45, hlam, hphi, ht23, ht34, p2229_1, u2ehi3]
                      · have p2229_0 := h2229c.1
                        have p2229_1 := h2229c.2.1
                        have p2229_2 := h2229c.2.2.1
                        have p2229_3 := h2229c.2.2.2
                        linarith only [hlam, p2229_0]
                · linarith only [h1961, h2223, h2224, h451, h560, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h2223, h559, h561, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h1965, h451, h560, hlam]
        · linarith only [h1964, h451, h559, h561, hc45, hlam, hphi, ht34, u3ehi0]
      · linarith only [h0, h1963, h556, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1962, h556, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, h1961, h556, hlam]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h561 | h561
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  linarith only [h559, h560, hc35, hlam, hphi, u3ehi3]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h560 | h560
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560

end R2N4
