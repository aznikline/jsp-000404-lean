import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1970 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1971 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1972 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1973 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1975 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1976 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1977 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 2 3 5 (by decide) (by decide) with h1978 | h1978
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1979 | h1979
    · rcases m.htr 3 4 5 (by decide) (by decide) with h1980 | h1980
      · rcases h0bigk with h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [hlam, p1981_0]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [h0, hlam, p1981_1]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [h1414, hlam, p1981_0]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [h1728, h1970, hlam, p1981_1]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [h1728, hlam, p1981_1]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          rcases p1981_3 (m.d 0 1) (by simp) with h1987 | h1987
          · linarith only [h0, h1987, hlam]
          · rcases p1981_3 (m.d 0 2) (by simp) with h1989 | h1989
            · rcases p1981_3 (m.d 0 3) (by simp) with h1990 | h1990
              · linarith only [h1965, h1990, hlam]
              · linarith only [h1414, h1990, hlam]
            · linarith only [h0, h1989, hlam]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [hlam, p1981_0]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [h0, h1965, h1977, h1980, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1981_1]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          rcases p1981_3 (m.d 0 1) (by simp) with h1996 | h1996
          · linarith only [h0, h1996, hlam]
          · rcases p1981_3 (m.d 0 2) (by simp) with h1998 | h1998
            · rcases p1981_3 (m.d 0 3) (by simp) with h1999 | h1999
              · linarith only [h1965, h1999, hlam]
              · linarith only [h1968, h1999, hlam]
            · linarith only [h1966, h1998, hlam]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          rcases p1981_3 (m.d 0 1) (by simp) with h2003 | h2003
          · linarith only [h0, h2003, hlam]
          · rcases p1981_3 (m.d 0 2) (by simp) with h2005 | h2005
            · rcases p1981_3 (m.d 0 3) (by simp) with h2006 | h2006
              · linarith only [h1965, h2006, hlam]
              · linarith only [h1969, h2006, hlam]
            · linarith only [h1967, h2005, hlam]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          rcases p1981_3 (m.d 0 1) (by simp) with h2010 | h2010
          · linarith only [h1414, h2010, hlam]
          · rcases p1981_3 (m.d 0 2) (by simp) with h2012 | h2012
            · rcases p1981_3 (m.d 0 3) (by simp) with h2013 | h2013
              · rcases p1981_3 (m.d 0 4) (by simp) with h2014 | h2014
                · linarith only [h1968, h2014, hlam]
                · linarith only [h1728, h1970, h2014, hlam]
              · linarith only [h1414, h2013, hlam]
            · linarith only [h0, h2012, hlam]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [h1965, hlam, p1981_1]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [hlam, p1981_0]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          rcases p1981_3 (m.d 0 1) (by simp) with h2021 | h2021
          · linarith only [h1414, h2021, hlam]
          · rcases p1981_3 (m.d 0 2) (by simp) with h2023 | h2023
            · rcases p1981_3 (m.d 0 3) (by simp) with h2024 | h2024
              · rcases p1981_3 (m.d 0 4) (by simp) with h2025 | h2025
                · linarith only [h1968, h2025, hlam]
                · rcases p1981_3 (m.d 0 5) (by simp) with h2027 | h2027
                  · linarith only [h1969, h2027, hlam]
                  · rcases h0emax with h2029 | h2029 | h2029 | h2029 | h2029
                    · rcases h5bigk with h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [hlam, p2030_0]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1728, hlam, p2030_1]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h0, h1965, h1970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1981_1, p2030_1, u2ehi4]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h0, h1965, h1970, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2030_1]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h0, h1965, h1970, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2030_1]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1728, h1976, hc01, hc14, hlam, hphi, p2030_1]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [hlam, p2030_0]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1972, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2030_1, u2ehi4]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        rcases p2030_3 (m.d 0 5) (by simp) with h2039 | h2039
                        · linarith only [h1728, h2039, hlam]
                        · linarith only [h1969, h2039, hlam]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        rcases p2030_3 (m.d 0 5) (by simp) with h2042 | h2042
                        · linarith only [h1728, h2042, hlam]
                        · linarith only [h1970, h2042, hlam]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1967, hlam, p2030_1]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1973, hlam, p2030_1]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [hlam, p2030_0]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h0, h1967, h1980, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2030_1]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h0, h1965, h1967, h1970, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2030_1]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1969, hlam, p2030_0]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1975, hlam, p2030_0]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1978, hlam, p2030_0]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [hlam, p2030_0]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h0, h1965, h1969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2030_1]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1970, hlam, p2030_0]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1976, hlam, p2030_0]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1979, hlam, p2030_0]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [h1980, hlam, p2030_0]
                      · have p2030_0 := h2030c.1
                        have p2030_1 := h2030c.2.1
                        have p2030_2 := h2030c.2.2.1
                        have p2030_3 := h2030c.2.2.2
                        linarith only [hlam, p2030_0]
                    · linarith only [h1965, h2029, hc04, hlam, hphi, ht0b, ht45, ht5b, p1981_1]
                    · linarith only [h1967, h1970, h2029, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1981_1, u2ehi4]
                    · rcases h5bigk with h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c | h2062c
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [hlam, p2062_0]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1728, hlam, p2062_1]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1965, h1970, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1981_1, p2062_1, u2ehi4]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h0, h1965, h1970, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2062_1]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h0, h1965, h1970, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2062_1]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1728, h1971, h1974, h1976, hc01, hc12, hlam, hphi, p2062_1]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [hlam, p2062_0]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1971, h1974, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2062_1, u2ehi4]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        rcases p2062_3 (m.d 0 5) (by simp) with h2071 | h2071
                        · linarith only [h1728, h2071, hlam]
                        · linarith only [h1969, h2071, hlam]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        rcases p2062_3 (m.d 0 5) (by simp) with h2074 | h2074
                        · linarith only [h1728, h2074, hlam]
                        · linarith only [h1970, h2074, hlam]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1967, hlam, p2062_1]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1973, hlam, p2062_1]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [hlam, p2062_0]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h0, h1966, h1979, h1980, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2062_1]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h0, h1965, h1966, h1979, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2062_1]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1969, hlam, p2062_0]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1975, hlam, p2062_0]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1978, hlam, p2062_0]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [hlam, p2062_0]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h0, h1965, h1969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2062_1]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1970, hlam, p2062_0]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1976, hlam, p2062_0]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1979, hlam, p2062_0]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [h1980, hlam, p2062_0]
                      · have p2062_0 := h2062c.1
                        have p2062_1 := h2062c.2.1
                        have p2062_2 := h2062c.2.2.1
                        have p2062_3 := h2062c.2.2.2
                        linarith only [hlam, p2062_0]
                    · rcases h5bigk with h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [hlam, p2092_0]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1728, hlam, p2092_1]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2092_1, u2ehi4]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h0, h1965, h1970, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2092_1]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h0, h1965, h1970, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2092_1]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1728, h1971, h1974, h1976, hc01, hc12, hlam, hphi, p2092_1]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [hlam, p2092_0]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1971, h1974, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2092_1, u2ehi4]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        rcases p2092_3 (m.d 0 5) (by simp) with h2101 | h2101
                        · linarith only [h1728, h2101, hlam]
                        · linarith only [h1969, h2101, hlam]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        rcases p2092_3 (m.d 0 5) (by simp) with h2104 | h2104
                        · linarith only [h1728, h2104, hlam]
                        · linarith only [h1970, h2104, hlam]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1967, hlam, p2092_1]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1973, hlam, p2092_1]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [hlam, p2092_0]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h0, h1967, h1980, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2092_1]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h0, h1965, h1967, h1970, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2092_1]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1969, hlam, p2092_0]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1975, hlam, p2092_0]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1978, hlam, p2092_0]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [hlam, p2092_0]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h0, h1965, h1969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2092_1]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1970, hlam, p2092_0]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1976, hlam, p2092_0]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1979, hlam, p2092_0]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [h1980, hlam, p2092_0]
                      · have p2092_0 := h2092c.1
                        have p2092_1 := h2092c.2.1
                        have p2092_2 := h2092c.2.2.1
                        have p2092_3 := h2092c.2.2.2
                        linarith only [hlam, p2092_0]
              · linarith only [h1968, h2024, hlam]
            · linarith only [h1966, h2023, hlam]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          rcases p1981_3 (m.d 0 1) (by simp) with h2124 | h2124
          · linarith only [h1414, h2124, hlam]
          · rcases p1981_3 (m.d 0 2) (by simp) with h2126 | h2126
            · rcases p1981_3 (m.d 0 3) (by simp) with h2127 | h2127
              · rcases p1981_3 (m.d 0 4) (by simp) with h2128 | h2128
                · linarith only [h1968, h2128, hlam]
                · linarith only [h1970, h2128, hlam]
              · linarith only [h1969, h2127, hlam]
            · linarith only [h1967, h2126, hlam]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          rcases p1981_3 (m.d 0 1) (by simp) with h2133 | h2133
          · linarith only [h2133, hlam, p1981_0]
          · rcases p1981_3 (m.d 0 2) (by simp) with h2135 | h2135
            · rcases p1981_3 (m.d 0 3) (by simp) with h2136 | h2136
              · rcases p1981_3 (m.d 0 4) (by simp) with h2137 | h2137
                · rcases p1981_3 (m.d 0 5) (by simp) with h2138 | h2138
                  · linarith only [h1970, h2138, hlam]
                  · linarith only [h1728, h2138, hlam]
                · linarith only [h2137, hlam, p1981_0]
              · linarith only [h1414, h2136, hlam]
            · linarith only [h0, h2135, hlam]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [h1966, hlam, p1981_0]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [h1968, hlam, p1981_0]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [hlam, p1981_0]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          rcases p1981_3 (m.d 0 1) (by simp) with h2147 | h2147
          · linarith only [h0, h1967, h2147, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1981_1, u2ehi4]
          · rcases p1981_3 (m.d 0 2) (by simp) with h2149 | h2149
            · rcases p1981_3 (m.d 0 3) (by simp) with h2150 | h2150
              · rcases p1981_3 (m.d 0 4) (by simp) with h2151 | h2151
                · rcases p1981_3 (m.d 0 5) (by simp) with h2152 | h2152
                  · linarith only [h1970, h2152, hlam]
                  · rcases h0emax with h2154 | h2154 | h2154 | h2154 | h2154
                    · rcases h5bigk with h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [hlam, p2155_0]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1728, hlam, p2155_1]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1981_1, p2155_1, u2ehi4]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2155_1]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2155_1]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1728, h1971, h1974, h1976, hc01, hc12, hlam, hphi, p2155_1]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [hlam, p2155_0]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1971, h1974, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2155_1, u2ehi4]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        rcases p2155_3 (m.d 0 5) (by simp) with h2164 | h2164
                        · linarith only [h1728, h2164, hlam]
                        · linarith only [h1969, h2164, hlam]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        rcases p2155_3 (m.d 0 5) (by simp) with h2167 | h2167
                        · linarith only [h1728, h2167, hlam]
                        · linarith only [h1970, h2167, hlam]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1967, hlam, p2155_1]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1973, hlam, p2155_1]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [hlam, p2155_0]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h0, h1967, h1980, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2155_1]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h0, h1965, h1967, h1968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2155_1]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1969, hlam, p2155_0]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1975, hlam, p2155_0]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1978, hlam, p2155_0]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [hlam, p2155_0]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h0, h1965, h1969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2155_1]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1970, hlam, p2155_0]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1976, hlam, p2155_0]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1979, hlam, p2155_0]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [h1980, hlam, p2155_0]
                      · have p2155_0 := h2155c.1
                        have p2155_1 := h2155c.2.1
                        have p2155_2 := h2155c.2.2.1
                        have p2155_3 := h2155c.2.2.2
                        linarith only [hlam, p2155_0]
                    · linarith only [h1965, h1968, h2154, hc05, hlam, hphi, ht0b, ht5b, p1981_1]
                    · linarith only [h1967, h1968, h2154, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1981_1, u2ehi4]
                    · linarith only [h1967, h2154, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1981_1, u2ehi4]
                    · rcases h5bigk with h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [hlam, p2188_0]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1728, hlam, p2188_1]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1965, h1968, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1981_1, p2188_1, u2ehi4]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2188_1]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2188_1]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1728, h1971, h1974, h1976, hc01, hc12, hlam, hphi, p2188_1]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [hlam, p2188_0]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1971, h1974, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2188_1, u2ehi4]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        rcases p2188_3 (m.d 0 5) (by simp) with h2197 | h2197
                        · linarith only [h1728, h2197, hlam]
                        · linarith only [h1969, h2197, hlam]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        rcases p2188_3 (m.d 0 5) (by simp) with h2200 | h2200
                        · linarith only [h1728, h2200, hlam]
                        · linarith only [h1970, h2200, hlam]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1967, hlam, p2188_1]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1973, hlam, p2188_1]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [hlam, p2188_0]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h0, h1967, h1980, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2188_1]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h0, h1965, h1967, h1968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1981_1, p2188_1]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1969, hlam, p2188_0]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1975, hlam, p2188_0]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1978, hlam, p2188_0]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [hlam, p2188_0]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h0, h1965, h1969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2188_1]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1970, hlam, p2188_0]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1976, hlam, p2188_0]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1979, hlam, p2188_0]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [h1980, hlam, p2188_0]
                      · have p2188_0 := h2188c.1
                        have p2188_1 := h2188c.2.1
                        have p2188_2 := h2188c.2.2.1
                        have p2188_3 := h2188c.2.2.2
                        linarith only [hlam, p2188_0]
                · linarith only [h1970, h2151, hlam]
              · linarith only [h1969, h2150, hlam]
            · linarith only [h1967, h2149, hlam]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          rcases p1981_3 (m.d 0 1) (by simp) with h2221 | h2221
          · linarith only [h1728, h2221, hlam]
          · rcases p1981_3 (m.d 0 2) (by simp) with h2223 | h2223
            · rcases p1981_3 (m.d 0 3) (by simp) with h2224 | h2224
              · rcases p1981_3 (m.d 0 4) (by simp) with h2225 | h2225
                · rcases p1981_3 (m.d 0 5) (by simp) with h2226 | h2226
                  · rcases h0emax with h2227 | h2227 | h2227 | h2227 | h2227
                    · rcases h5bigk with h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [hlam, p2228_0]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1728, hlam, p2228_1]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2228_1, u2ehi4]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        rcases p2228_3 (m.d 0 5) (by simp) with h2232 | h2232
                        · rcases p2228_3 (m.d 1 5) (by simp) with h2233 | h2233
                          · rcases p2228_3 (m.d 2 5) (by simp) with h2234 | h2234
                            · linarith only [h1967, h2234, hlam]
                            · linarith only [h1978, h2234, hlam]
                          · linarith only [h1975, h2233, hlam]
                        · linarith only [h1969, h2232, hlam]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        rcases p2228_3 (m.d 0 5) (by simp) with h2239 | h2239
                        · rcases p2228_3 (m.d 1 5) (by simp) with h2240 | h2240
                          · rcases p2228_3 (m.d 2 5) (by simp) with h2241 | h2241
                            · linarith only [h1967, h2241, hlam]
                            · linarith only [h1979, h2241, hlam]
                          · linarith only [h1976, h2240, hlam]
                        · linarith only [h1970, h2239, hlam]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1971, h1974, h1976, hc01, hc12, hlam, hphi, p1981_1, p2228_1]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [hlam, p2228_0]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1971, h1974, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2228_1, u2ehi4]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        rcases p2228_3 (m.d 0 5) (by simp) with h2249 | h2249
                        · linarith only [h1728, h2249, hlam]
                        · linarith only [h1969, h2249, hlam]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        rcases p2228_3 (m.d 0 5) (by simp) with h2252 | h2252
                        · linarith only [h1728, h2252, hlam]
                        · linarith only [h1970, h2252, hlam]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1967, hlam, p2228_1]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1973, hlam, p2228_1]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [hlam, p2228_0]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h0, h1967, h1980, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2228_1]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h0, h1965, h1977, h1979, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2228_1]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1969, hlam, p2228_0]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1975, hlam, p2228_0]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1978, hlam, p2228_0]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [hlam, p2228_0]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h0, h1965, h1969, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2228_1]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1970, hlam, p2228_0]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1976, hlam, p2228_0]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1979, hlam, p2228_0]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [h1980, hlam, p2228_0]
                      · have p2228_0 := h2228c.1
                        have p2228_1 := h2228c.2.1
                        have p2228_2 := h2228c.2.2.1
                        have p2228_3 := h2228c.2.2.2
                        linarith only [hlam, p2228_0]
                    · linarith only [h1965, h1977, h2227, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h1968, h1970, h2227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1981_1]
                    · linarith only [h1970, h2227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1981_1]
                    · linarith only [h2227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1981_1]
                  · linarith only [h1728, h2226, hlam]
                · linarith only [h1970, h2225, hlam, p1981_1]
              · linarith only [h1414, h2224, hlam]
            · linarith only [h0, h2223, hlam]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [h1967, hlam, p1981_1]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [h1969, hlam, p1981_0]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [h1970, hlam, p1981_1]
        · have p1981_0 := h1981c.1
          have p1981_1 := h1981c.2.1
          have p1981_2 := h1981c.2.2.1
          have p1981_3 := h1981c.2.2.2
          linarith only [hlam, p1981_0]
      · rcases h0bigk with h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c | h2282c
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [hlam, p2282_0]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h0, hlam, p2282_1]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h1414, hlam, p2282_0]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h1966, h1979, h1980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2282_1]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h1728, hlam, p2282_1]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          rcases p2282_3 (m.d 0 1) (by simp) with h2288 | h2288
          · linarith only [h0, h2288, hlam]
          · rcases p2282_3 (m.d 0 2) (by simp) with h2290 | h2290
            · rcases p2282_3 (m.d 0 3) (by simp) with h2291 | h2291
              · linarith only [h1965, h2291, hlam]
              · linarith only [h1414, h2291, hlam]
            · linarith only [h0, h2290, hlam]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [hlam, p2282_0]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h1966, h1968, h1979, h1980, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2282_1]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h0, h1966, h1979, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2282_1]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          rcases p2282_3 (m.d 0 1) (by simp) with h2298 | h2298
          · linarith only [h0, h2298, hlam]
          · rcases p2282_3 (m.d 0 2) (by simp) with h2300 | h2300
            · rcases p2282_3 (m.d 0 3) (by simp) with h2301 | h2301
              · linarith only [h1965, h2301, hlam]
              · linarith only [h1969, h2301, hlam]
            · linarith only [h1967, h2300, hlam]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          rcases p2282_3 (m.d 0 1) (by simp) with h2305 | h2305
          · linarith only [h1414, h2305, hlam]
          · rcases p2282_3 (m.d 0 2) (by simp) with h2307 | h2307
            · rcases p2282_3 (m.d 0 3) (by simp) with h2308 | h2308
              · rcases p2282_3 (m.d 0 4) (by simp) with h2309 | h2309
                · linarith only [h1968, h2309, hlam]
                · linarith only [h1966, h1979, h1980, h2309, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2282_1]
              · linarith only [h1414, h2308, hlam]
            · linarith only [h0, h2307, hlam]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h1965, hlam, p2282_1]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [hlam, p2282_0]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h0, h1965, h1966, h1979, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2282_1]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          rcases p2282_3 (m.d 0 1) (by simp) with h2317 | h2317
          · linarith only [h1414, h2317, hlam]
          · rcases p2282_3 (m.d 0 2) (by simp) with h2319 | h2319
            · rcases p2282_3 (m.d 0 3) (by simp) with h2320 | h2320
              · rcases p2282_3 (m.d 0 4) (by simp) with h2321 | h2321
                · linarith only [h1968, h2321, hlam]
                · linarith only [h1970, h2321, hlam]
              · linarith only [h1969, h2320, hlam]
            · linarith only [h1967, h2319, hlam]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          rcases p2282_3 (m.d 0 1) (by simp) with h2326 | h2326
          · linarith only [h2326, hlam, p2282_0]
          · rcases p2282_3 (m.d 0 2) (by simp) with h2328 | h2328
            · rcases p2282_3 (m.d 0 3) (by simp) with h2329 | h2329
              · rcases p2282_3 (m.d 0 4) (by simp) with h2330 | h2330
                · rcases p2282_3 (m.d 0 5) (by simp) with h2331 | h2331
                  · linarith only [h1970, h2331, hlam]
                  · linarith only [h1728, h2331, hlam]
                · linarith only [h2330, hlam, p2282_0]
              · linarith only [h1414, h2329, hlam]
            · linarith only [h0, h2328, hlam]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h1966, hlam, p2282_0]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h1968, hlam, p2282_0]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [hlam, p2282_0]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          rcases p2282_3 (m.d 0 1) (by simp) with h2340 | h2340
          · linarith only [h1728, h2340, hlam, p2282_1]
          · rcases p2282_3 (m.d 0 2) (by simp) with h2342 | h2342
            · rcases p2282_3 (m.d 0 3) (by simp) with h2343 | h2343
              · rcases p2282_3 (m.d 0 4) (by simp) with h2344 | h2344
                · rcases p2282_3 (m.d 0 5) (by simp) with h2345 | h2345
                  · linarith only [h1970, h2345, hlam]
                  · rcases h0emax with h2347 | h2347 | h2347 | h2347 | h2347
                    · rcases h5bigk with h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c | h2348c
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [hlam, p2348_0]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1728, hlam, p2348_1]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2282_1, p2348_1, u2ehi4]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2282_1, p2348_1]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h0, h1965, h1968, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2282_1, p2348_1]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1728, h1976, hc01, hc14, hlam, hphi, p2348_1]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [hlam, p2348_0]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1972, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2348_1, u2ehi4]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        rcases p2348_3 (m.d 0 5) (by simp) with h2357 | h2357
                        · linarith only [h1728, h2357, hlam]
                        · linarith only [h1969, h2357, hlam]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1971, h1974, h1976, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2348_1]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1967, hlam, p2348_1]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1973, hlam, p2348_1]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [hlam, p2348_0]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h0, h1967, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2348_1]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h0, h1965, h1967, h1968, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2282_1, p2348_1]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1969, hlam, p2348_0]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1975, hlam, p2348_0]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1978, hlam, p2348_0]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [hlam, p2348_0]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1980, hlam, p2348_1]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1970, hlam, p2348_0]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1976, hlam, p2348_0]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1979, hlam, p2348_0]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [h1977, h1979, h1980, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2348_1]
                      · have p2348_0 := h2348c.1
                        have p2348_1 := h2348c.2.1
                        have p2348_2 := h2348c.2.2.1
                        have p2348_3 := h2348c.2.2.2
                        linarith only [hlam, p2348_0]
                    · linarith only [h1965, h1967, h1968, h2347, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2282_1, u2ehi4]
                    · linarith only [h1967, h1968, h2347, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2282_1, u2ehi4]
                    · linarith only [h1967, h2347, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2282_1, u2ehi4]
                    · rcases h5bigk with h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [hlam, p2379_0]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1728, hlam, p2379_1]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2282_1, p2379_1, u2ehi4]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h0, h1965, h1968, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2282_1, p2379_1]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h0, h1965, h1968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2282_1, p2379_1]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1728, h1971, h1974, h1976, hc01, hc12, hlam, hphi, p2379_1]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [hlam, p2379_0]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1971, h1974, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2379_1, u2ehi4]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        rcases p2379_3 (m.d 0 5) (by simp) with h2388 | h2388
                        · linarith only [h1728, h2388, hlam]
                        · linarith only [h1969, h2388, hlam]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1971, h1974, h1976, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2379_1]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1967, hlam, p2379_1]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1973, hlam, p2379_1]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [hlam, p2379_0]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h0, h1967, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2379_1]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h0, h1965, h1967, h1968, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2282_1, p2379_1]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1969, hlam, p2379_0]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1975, hlam, p2379_0]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1978, hlam, p2379_0]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [hlam, p2379_0]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1980, hlam, p2379_1]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1970, hlam, p2379_0]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1976, hlam, p2379_0]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1979, hlam, p2379_0]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [h1980, hc34, hc45, hlam, hphi, p2379_1]
                      · have p2379_0 := h2379c.1
                        have p2379_1 := h2379c.2.1
                        have p2379_2 := h2379c.2.2.1
                        have p2379_3 := h2379c.2.2.2
                        linarith only [hlam, p2379_0]
                · linarith only [h1970, h2344, hlam]
              · linarith only [h1969, h2343, hlam]
            · linarith only [h1967, h2342, hlam]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          rcases p2282_3 (m.d 0 1) (by simp) with h2410 | h2410
          · linarith only [h1728, h2410, hlam]
          · rcases p2282_3 (m.d 0 2) (by simp) with h2412 | h2412
            · rcases p2282_3 (m.d 0 3) (by simp) with h2413 | h2413
              · rcases p2282_3 (m.d 0 4) (by simp) with h2414 | h2414
                · rcases p2282_3 (m.d 0 5) (by simp) with h2415 | h2415
                  · rcases h0emax with h2416 | h2416 | h2416 | h2416 | h2416
                    · rcases h5bigk with h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [hlam, p2417_0]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1728, hlam, p2417_1]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2417_1, u2ehi4]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        rcases p2417_3 (m.d 0 5) (by simp) with h2421 | h2421
                        · rcases p2417_3 (m.d 1 5) (by simp) with h2422 | h2422
                          · rcases p2417_3 (m.d 2 5) (by simp) with h2423 | h2423
                            · linarith only [h1967, h2423, hlam]
                            · linarith only [h1978, h2423, hlam]
                          · linarith only [h1975, h2422, hlam]
                        · linarith only [h1969, h2421, hlam]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1728, h1971, h1974, h1976, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2417_1]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1971, h1974, h1976, hc01, hc12, hlam, hphi, p2282_1, p2417_1]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [hlam, p2417_0]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1971, h1974, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2417_1, u2ehi4]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        rcases p2417_3 (m.d 0 5) (by simp) with h2432 | h2432
                        · linarith only [h1728, h2432, hlam]
                        · linarith only [h1969, h2432, hlam]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1971, h1974, h1976, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2417_1]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1967, hlam, p2417_1]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1973, hlam, p2417_1]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [hlam, p2417_0]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h0, h1967, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2417_1]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h0, h1965, h1977, h1979, h1980, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2417_1]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1969, hlam, p2417_0]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1975, hlam, p2417_0]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1978, hlam, p2417_0]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [hlam, p2417_0]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1980, hlam, p2417_1]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1970, hlam, p2417_0]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1976, hlam, p2417_0]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1979, hlam, p2417_0]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [h1980, hc34, hc45, hlam, hphi, p2417_1]
                      · have p2417_0 := h2417c.1
                        have p2417_1 := h2417c.2.1
                        have p2417_2 := h2417c.2.2.1
                        have p2417_3 := h2417c.2.2.2
                        linarith only [hlam, p2417_0]
                    · linarith only [h1965, h1977, h1979, h2416, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1968, h1970, h2416, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2282_1]
                    · linarith only [h1970, h2416, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2282_1]
                    · linarith only [h2416, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2282_1]
                  · linarith only [h1728, h2415, hlam]
                · linarith only [h1970, h2414, hlam, p2282_1]
              · linarith only [h1414, h2413, hlam]
            · linarith only [h0, h2412, hlam]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h1967, hlam, p2282_1]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h1969, hlam, p2282_0]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [h1970, hlam, p2282_1]
        · have p2282_0 := h2282c.1
          have p2282_1 := h2282c.2.1
          have p2282_2 := h2282c.2.2.1
          have p2282_3 := h2282c.2.2.2
          linarith only [hlam, p2282_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2463 | h2463
      · linarith only [h1979, h2463, hc34, hlam, hphi, ht23, u2ehi3]
      · rcases h0bigk with h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c | h2465c
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [hlam, p2465_0]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h0, hlam, p2465_1]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1414, hlam, p2465_0]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1970, h1979, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2465_1, u2ehi3]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1728, hlam, p2465_1]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          rcases p2465_3 (m.d 0 1) (by simp) with h2471 | h2471
          · linarith only [h0, h2471, hlam]
          · rcases p2465_3 (m.d 0 2) (by simp) with h2473 | h2473
            · rcases p2465_3 (m.d 0 3) (by simp) with h2474 | h2474
              · linarith only [h1965, h2474, hlam]
              · linarith only [h1414, h2474, hlam]
            · linarith only [h0, h2473, hlam]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [hlam, p2465_0]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1968, h1970, h1979, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2465_1, u2ehi3]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h0, h1970, h1979, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2465_1, u2ehi3]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h0, h1970, h1979, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2465_1, u2ehi3]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          rcases p2465_3 (m.d 0 1) (by simp) with h2482 | h2482
          · linarith only [h1414, h2482, hlam]
          · rcases p2465_3 (m.d 0 2) (by simp) with h2484 | h2484
            · rcases p2465_3 (m.d 0 3) (by simp) with h2485 | h2485
              · rcases p2465_3 (m.d 0 4) (by simp) with h2486 | h2486
                · linarith only [h1968, h2486, hlam]
                · linarith only [h1970, h1979, h2486, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2465_1, u2ehi3]
              · linarith only [h1414, h2485, hlam]
            · linarith only [h0, h2484, hlam]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1965, hlam, p2465_1]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [hlam, p2465_0]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1970, h1979, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2465_1, u2ehi3]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1414, h1970, h1971, h1979, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2465_1, u2ehi3]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          rcases p2465_3 (m.d 0 1) (by simp) with h2495 | h2495
          · linarith only [h2495, hlam, p2465_0]
          · rcases p2465_3 (m.d 0 2) (by simp) with h2497 | h2497
            · rcases p2465_3 (m.d 0 3) (by simp) with h2498 | h2498
              · rcases p2465_3 (m.d 0 4) (by simp) with h2499 | h2499
                · rcases p2465_3 (m.d 0 5) (by simp) with h2500 | h2500
                  · linarith only [h1970, h2500, hlam]
                  · linarith only [h1728, h2500, hlam]
                · linarith only [h2499, hlam, p2465_0]
              · linarith only [h1414, h2498, hlam]
            · linarith only [h0, h2497, hlam]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1966, hlam, p2465_0]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1968, hlam, p2465_0]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [hlam, p2465_0]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1970, h1979, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2465_1, u2ehi3]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          rcases p2465_3 (m.d 0 1) (by simp) with h2510 | h2510
          · linarith only [h1728, h2510, hlam]
          · rcases p2465_3 (m.d 0 2) (by simp) with h2512 | h2512
            · rcases p2465_3 (m.d 0 3) (by simp) with h2513 | h2513
              · rcases p2465_3 (m.d 0 4) (by simp) with h2514 | h2514
                · rcases p2465_3 (m.d 0 5) (by simp) with h2515 | h2515
                  · rcases h0emax with h2516 | h2516 | h2516 | h2516 | h2516
                    · rcases h5bigk with h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1728, hlam, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2517_1, u2ehi4]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        rcases p2517_3 (m.d 0 5) (by simp) with h2521 | h2521
                        · rcases p2517_3 (m.d 1 5) (by simp) with h2522 | h2522
                          · rcases p2517_3 (m.d 2 5) (by simp) with h2523 | h2523
                            · linarith only [h1967, h2523, hlam]
                            · linarith only [h1978, h2523, hlam]
                          · linarith only [h1975, h2522, hlam]
                        · linarith only [h1969, h2521, hlam]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1728, h1971, h1974, h1976, h1979, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2517_1, u2ehi3]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1971, h1974, h1976, hc01, hc12, hlam, hphi, p2465_1, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1971, h1974, h1976, h1979, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2517_1, u2ehi3]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        rcases p2517_3 (m.d 0 5) (by simp) with h2532 | h2532
                        · linarith only [h1728, h2532, hlam]
                        · linarith only [h1969, h2532, hlam]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1971, h1974, h1976, h1979, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2517_1, u2ehi3]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1967, hlam, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1973, hlam, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h0, h1967, h2463, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1979, hlam, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1969, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1975, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1978, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h2463, hlam, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1970, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1976, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hc45, hlam, hphi, ht23, ht34, p2517_1, u2ehi4]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1414, h1968, h1970, h1971, h2463, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hlam, p2517_0]
                    · linarith only [h1965, h2516, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h1969, h2516, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2465_1]
                    · linarith only [h1970, h1979, h2516, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h0, h1965, h1968, h1970, h1979, h2516, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2465_1, u2ehi3]
                  · linarith only [h1728, h2515, hlam]
                · linarith only [h1970, h1979, h2514, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2465_1, u2ehi3]
              · linarith only [h1414, h2513, hlam]
            · linarith only [h0, h2512, hlam]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1967, hlam, p2465_1]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1969, hlam, p2465_0]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [h1970, hlam, p2465_1]
        · have p2465_0 := h2465c.1
          have p2465_1 := h2465c.2.1
          have p2465_2 := h2465c.2.2.1
          have p2465_3 := h2465c.2.2.2
          linarith only [hlam, p2465_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h2563 | h2563
    · linarith only [h1977, h1978, h2563, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2565 | h2565
      · linarith only [h2563, h2565, hc34, hlam, hphi, ht23, u2ehi3]
      · rcases h0bigk with h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [hlam, p2567_0]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h0, hlam, p2567_1]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1414, hlam, p2567_0]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1970, h1977, h1978, h2565, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2567_1, u2ehi3]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1728, hlam, p2567_1]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          rcases p2567_3 (m.d 0 1) (by simp) with h2573 | h2573
          · linarith only [h0, h2573, hlam]
          · rcases p2567_3 (m.d 0 2) (by simp) with h2575 | h2575
            · rcases p2567_3 (m.d 0 3) (by simp) with h2576 | h2576
              · linarith only [h1965, h2576, hlam]
              · linarith only [h1414, h2576, hlam]
            · linarith only [h0, h2575, hlam]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [hlam, p2567_0]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1968, h1970, h1977, h1978, h2565, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2567_1, u2ehi3]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h0, h1970, h1977, h1978, h2565, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2567_1, u2ehi3]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h0, h1970, h1977, h1978, h2565, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2567_1, u2ehi3]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          rcases p2567_3 (m.d 0 1) (by simp) with h2584 | h2584
          · linarith only [h1414, h2584, hlam]
          · rcases p2567_3 (m.d 0 2) (by simp) with h2586 | h2586
            · rcases p2567_3 (m.d 0 3) (by simp) with h2587 | h2587
              · rcases p2567_3 (m.d 0 4) (by simp) with h2588 | h2588
                · linarith only [h1968, h2588, hlam]
                · linarith only [h1970, h1977, h1978, h2565, h2588, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2567_1, u2ehi3]
              · linarith only [h1414, h2587, hlam]
            · linarith only [h0, h2586, hlam]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1965, hlam, p2567_1]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [hlam, p2567_0]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1970, h1977, h1978, h2565, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2567_1, u2ehi3]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1414, h1970, h1971, h1977, h1978, h2565, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2567_1, u2ehi3]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          rcases p2567_3 (m.d 0 1) (by simp) with h2597 | h2597
          · linarith only [h2597, hlam, p2567_0]
          · rcases p2567_3 (m.d 0 2) (by simp) with h2599 | h2599
            · rcases p2567_3 (m.d 0 3) (by simp) with h2600 | h2600
              · rcases p2567_3 (m.d 0 4) (by simp) with h2601 | h2601
                · rcases p2567_3 (m.d 0 5) (by simp) with h2602 | h2602
                  · linarith only [h1970, h2602, hlam]
                  · linarith only [h1728, h2602, hlam]
                · linarith only [h2601, hlam, p2567_0]
              · linarith only [h1414, h2600, hlam]
            · linarith only [h0, h2599, hlam]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1966, hlam, p2567_0]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1968, hlam, p2567_0]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [hlam, p2567_0]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1414, h1968, h1970, h1971, h1977, h1978, h2565, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2567_1, u2ehi3]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          rcases p2567_3 (m.d 0 1) (by simp) with h2612 | h2612
          · linarith only [h1728, h2612, hlam]
          · rcases p2567_3 (m.d 0 2) (by simp) with h2614 | h2614
            · rcases p2567_3 (m.d 0 3) (by simp) with h2615 | h2615
              · rcases p2567_3 (m.d 0 4) (by simp) with h2616 | h2616
                · rcases p2567_3 (m.d 0 5) (by simp) with h2617 | h2617
                  · rcases h0emax with h2618 | h2618 | h2618 | h2618 | h2618
                    · rcases h5bigk with h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c | h2619c
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [hlam, p2619_0]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1728, hlam, p2619_1]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1977, h1978, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2619_1, u2ehi3]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1728, h1971, h1974, h1976, h1977, h1978, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2619_1, u2ehi3]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1728, h1971, h1974, h1976, h1977, h1978, h2565, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2619_1, u2ehi3]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1971, h1974, h1976, hc01, hc12, hlam, hphi, p2567_1, p2619_1]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [hlam, p2619_0]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1971, h1974, h1976, h1977, h1978, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2619_1, u2ehi3]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1971, h1974, h1976, h1977, h1978, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2619_1, u2ehi3]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1971, h1974, h1976, h1977, h1978, h2565, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2619_1, u2ehi3]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1967, hlam, p2619_1]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1973, hlam, p2619_1]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [hlam, p2619_0]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1978, hlam, p2619_1]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h2563, hlam, p2619_1]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1969, hlam, p2619_0]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1975, hlam, p2619_0]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1977, h1978, hc35, hlam, hphi, ht23, p2619_1, u2ehi3]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [hlam, p2619_0]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h2565, hlam, p2619_1]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1970, hlam, p2619_0]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1976, hlam, p2619_0]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1414, h1968, h1970, h1971, h1977, h1978, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2619_1, u2ehi3]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [h1414, h1968, h1970, h1971, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2619_1]
                      · have p2619_0 := h2619c.1
                        have p2619_1 := h2619c.2.1
                        have p2619_2 := h2619c.2.2.1
                        have p2619_3 := h2619c.2.2.2
                        linarith only [hlam, p2619_0]
                    · linarith only [h1965, h1977, h2618, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h1969, h1977, h1978, h2618, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h1970, h1977, h1978, h2565, h2618, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h2618, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2567_1]
                  · linarith only [h1728, h2617, hlam]
                · linarith only [h1970, h1977, h1978, h2565, h2616, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2567_1, u2ehi3]
              · linarith only [h1414, h2615, hlam]
            · linarith only [h0, h2614, hlam]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1967, hlam, p2567_1]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1969, hlam, p2567_0]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [h1970, hlam, p2567_1]
        · have p2567_0 := h2567c.1
          have p2567_1 := h2567c.2.1
          have p2567_2 := h2567c.2.2.1
          have p2567_3 := h2567c.2.2.2
          linarith only [hlam, p2567_0]

end R2N4
