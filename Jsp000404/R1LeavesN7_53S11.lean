import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_53S9
import Jsp000404.R1LeavesN7_53S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1157 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1283 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1344 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 3 5 (by decide) (by decide) with h1952 | h1952
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1953 | h1953
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1954 | h1954
      · linarith only [h0, h1344, h1952, h1954, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1956 | h1956
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1957 | h1957
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1958 | h1958
            · rcases h2bigk with h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1283, h1954, h1956, h3, h6, hlam, p1959_2]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                rcases p1959_3 (m.d 0 2) (by simp) with h1962 | h1962
                · rcases p1959_3 (m.d 1 2) (by simp) with h1963 | h1963
                  · linarith only [h0, h1963, hlam]
                  · rcases p1959_3 (m.d 2 3) (by simp) with h1965 | h1965
                    · linarith only [h1965, hlam, p1959_0]
                    · rcases p1959_3 (m.d 2 4) (by simp) with h1967 | h1967
                      · linarith only [h1967, h4, hlam]
                      · linarith only [h1954, h1967, hlam]
                · linarith only [h1962, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                rcases p1959_3 (m.d 0 2) (by simp) with h1971 | h1971
                · rcases p1959_3 (m.d 1 2) (by simp) with h1972 | h1972
                  · linarith only [h0, h1972, hlam]
                  · rcases p1959_3 (m.d 2 3) (by simp) with h1974 | h1974
                    · linarith only [h1974, h3, hlam]
                    · rcases p1959_3 (m.d 2 4) (by simp) with h1976 | h1976
                      · linarith only [h1976, hlam, p1959_0]
                      · rcases p1959_3 (m.d 2 5) (by simp) with h1978 | h1978
                        · linarith only [h1978, h5, hlam]
                        · rcases h4bigk with h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c | h1980c
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [hlam, p1980_0]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            rcases p1980_3 (m.d 0 4) (by simp) with h1982 | h1982
                            · rcases p1980_3 (m.d 1 4) (by simp) with h1983 | h1983
                              · linarith only [h1983, h2, hlam]
                              · rcases p1980_3 (m.d 2 4) (by simp) with h1985 | h1985
                                · linarith only [h1985, h4, hlam]
                                · linarith only [h1157, h1985, hlam]
                            · linarith only [h1982, h2, hlam]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            rcases p1980_3 (m.d 0 4) (by simp) with h1989 | h1989
                            · rcases p1980_3 (m.d 1 4) (by simp) with h1990 | h1990
                              · linarith only [h1990, h2, hlam]
                              · rcases p1980_3 (m.d 2 4) (by simp) with h1992 | h1992
                                · linarith only [h1992, h4, hlam]
                                · rcases p1980_3 (m.d 3 4) (by simp) with h1994 | h1994
                                  · linarith only [h1994, h6, hlam]
                                  · linarith only [h1954, h1994, hlam]
                            · linarith only [h1989, h4, hlam]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h0, h1344, h1952, h1958, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p1980_1]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            rcases p1980_3 (m.d 0 4) (by simp) with h1999 | h1999
                            · rcases p1980_3 (m.d 1 4) (by simp) with h2000 | h2000
                              · linarith only [h2, h2000, hlam]
                              · linarith only [h1953, h2000, hlam]
                            · linarith only [h1999, hlam, p1980_0]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h2, hlam, p1980_1]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [hlam, p1980_0]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h1157, hlam, p1980_0]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h1344, hlam, p1980_1]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h0, h1157, hc01, hc45, hlam, hphi, ht0b, ht5b, p1959_1, p1980_1]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h4, hlam, p1980_1]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1959_1, p1980_1]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [hlam, p1980_0]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h1954, hlam, p1980_1]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p1959_1, p1980_1]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h6, hlam, p1980_1]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h1344, h1952, h6, hc03, hc35, hlam, hphi, ht0b, ht5b, p1980_1]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h0, h1283, h1954, h1956, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1980_1]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [hlam, p1980_0]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            rcases p1980_3 (m.d 0 4) (by simp) with h2018 | h2018
                            · rcases p1980_3 (m.d 1 4) (by simp) with h2019 | h2019
                              · linarith only [h1344, h2019, hlam]
                              · linarith only [h1953, h2019, hlam]
                            · linarith only [h2018, h7, hlam]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h7, hlam, p1980_0]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h1953, hlam, p1980_0]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h1957, hlam, p1980_0]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [h1958, hlam, p1980_0]
                          · have p1980_0 := h1980c.1
                            have p1980_1 := h1980c.2.1
                            have p1980_2 := h1980c.2.2.1
                            have p1980_3 := h1980c.2.2.2
                            linarith only [hlam, p1980_0]
                · linarith only [h1971, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                rcases p1959_3 (m.d 0 2) (by simp) with h2029 | h2029
                · rcases p1959_3 (m.d 1 2) (by simp) with h2030 | h2030
                  · linarith only [h0, h2030, hlam]
                  · rcases p1959_3 (m.d 2 3) (by simp) with h2032 | h2032
                    · linarith only [h2032, h3, hlam]
                    · linarith only [h1956, h2032, hlam]
                · linarith only [h2029, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h0, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h8, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1157, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1283, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h3, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h0, h1954, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1954, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h0, h1283, h1954, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h4, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                rcases p1959_3 (m.d 0 2) (by simp) with h2047 | h2047
                · rcases p1959_3 (m.d 1 2) (by simp) with h2048 | h2048
                  · linarith only [h2048, hlam, p1959_0]
                  · rcases p1959_3 (m.d 2 3) (by simp) with h2050 | h2050
                    · linarith only [h1954, h2050, hlam]
                    · linarith only [h2050, h8, hlam]
                · linarith only [h0, h2047, hlam]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h0, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h0, h1283, h1954, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h5, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h0, h1954, h1956, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1956, hlam, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1957, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [hlam, p1959_0]
            · linarith only [h0, h1954, h1958, h3, h6, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h1157, h1953, h1957, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h1952, h1956, h8, hlam]
    · linarith only [h1344, h1952, h1953, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2066 | h2066
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2067 | h2067
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2068 | h2068
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2069 | h2069
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2070 | h2070
            · rcases h2bigk with h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [hlam, p2071_0]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h1344, h2067, h3, h8, hlam, p2071_2]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h0, h1344, h2067, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2071_1]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                rcases p2071_3 (m.d 0 2) (by simp) with h2075 | h2075
                · rcases p2071_3 (m.d 1 2) (by simp) with h2076 | h2076
                  · linarith only [h0, h2076, hlam]
                  · rcases p2071_3 (m.d 2 3) (by simp) with h2078 | h2078
                    · linarith only [h2078, h3, hlam]
                    · linarith only [h2067, h2078, hlam]
                · linarith only [h2075, hlam, p2071_0]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                rcases p2071_3 (m.d 0 2) (by simp) with h2082 | h2082
                · rcases p2071_3 (m.d 1 2) (by simp) with h2083 | h2083
                  · linarith only [h0, h2083, hlam]
                  · rcases p2071_3 (m.d 2 3) (by simp) with h2085 | h2085
                    · linarith only [h2085, h3, hlam]
                    · linarith only [h2068, h2085, hlam]
                · linarith only [h2082, hlam, p2071_0]
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
                linarith only [h8, hlam, p2071_0]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h1157, hlam, p2071_0]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h1283, hlam, p2071_0]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h3, hlam, p2071_0]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                rcases p2071_3 (m.d 0 2) (by simp) with h2095 | h2095
                · rcases p2071_3 (m.d 1 2) (by simp) with h2096 | h2096
                  · linarith only [h2096, hlam, p2071_0]
                  · rcases p2071_3 (m.d 2 3) (by simp) with h2098 | h2098
                    · rcases p2071_3 (m.d 2 4) (by simp) with h2099 | h2099
                      · linarith only [h2067, h2099, hlam]
                      · linarith only [h1157, h2099, hlam]
                    · linarith only [h2098, hlam, p2071_0]
                · linarith only [h0, h2095, hlam]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [hlam, p2071_0]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h1952, h2068, h2069, h8, hc12, hc23, hlam, hphi, p2071_1]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h0, h1952, h2068, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2071_1]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h4, hlam, p2071_0]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                rcases p2071_3 (m.d 0 2) (by simp) with h2108 | h2108
                · rcases p2071_3 (m.d 1 2) (by simp) with h2109 | h2109
                  · linarith only [h2109, hlam, p2071_0]
                  · rcases p2071_3 (m.d 2 3) (by simp) with h2111 | h2111
                    · rcases p2071_3 (m.d 2 4) (by simp) with h2112 | h2112
                      · rcases p2071_3 (m.d 2 5) (by simp) with h2113 | h2113
                        · linarith only [h2069, h2113, hlam]
                        · linarith only [h1283, h2113, hlam]
                      · linarith only [h2112, hlam, p2071_0]
                    · linarith only [h2111, h8, hlam]
                · linarith only [h0, h2108, hlam]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h2067, hlam, p2071_1]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [hlam, p2071_0]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h1952, h2068, h8, hc12, hc24, hlam, hphi, p2071_1]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h5, hlam, p2071_0]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                rcases p2071_3 (m.d 0 2) (by simp) with h2123 | h2123
                · rcases p2071_3 (m.d 1 2) (by simp) with h2124 | h2124
                  · linarith only [h2124, hlam, p2071_0]
                  · rcases p2071_3 (m.d 2 3) (by simp) with h2126 | h2126
                    · rcases p2071_3 (m.d 2 4) (by simp) with h2127 | h2127
                      · rcases p2071_3 (m.d 2 5) (by simp) with h2128 | h2128
                        · rcases h4bigk with h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [hlam, p2129_0]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            rcases p2129_3 (m.d 0 4) (by simp) with h2131 | h2131
                            · rcases p2129_3 (m.d 1 4) (by simp) with h2132 | h2132
                              · linarith only [h2, h2132, hlam]
                              · rcases p2129_3 (m.d 2 4) (by simp) with h2134 | h2134
                                · linarith only [h2134, h4, hlam]
                                · linarith only [h1157, h2134, hlam]
                            · linarith only [h2, h2131, hlam]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h0, h2069, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2071_1, p2129_1]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            rcases p2129_3 (m.d 0 4) (by simp) with h2139 | h2139
                            · rcases p2129_3 (m.d 1 4) (by simp) with h2140 | h2140
                              · linarith only [h2, h2140, hlam]
                              · rcases p2129_3 (m.d 2 4) (by simp) with h2142 | h2142
                                · linarith only [h2142, h4, hlam]
                                · linarith only [h2067, h2142, hlam]
                            · linarith only [h2139, h6, hlam]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            rcases p2129_3 (m.d 0 4) (by simp) with h2146 | h2146
                            · rcases p2129_3 (m.d 1 4) (by simp) with h2147 | h2147
                              · linarith only [h2, h2147, hlam]
                              · linarith only [h2066, h2147, hlam]
                            · linarith only [h2146, hlam, p2129_0]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h2, hlam, p2129_1]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [hlam, p2129_0]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h1157, hlam, p2129_0]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h1344, hlam, p2129_1]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h0, h1344, h2067, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p2129_1]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h4, hlam, p2129_1]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h0, h2066, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2129_1]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [hlam, p2129_0]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h0, h1344, h2067, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2129_1]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            rcases p2129_3 (m.d 0 4) (by simp) with h2160 | h2160
                            · rcases p2129_3 (m.d 1 4) (by simp) with h2161 | h2161
                              · linarith only [h1157, h2161, hlam]
                              · linarith only [h2066, h2161, hlam]
                            · linarith only [h2160, h7, hlam]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h6, hlam, p2129_1]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h0, h2066, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p2129_1]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h2067, hlam, p2129_0]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [hlam, p2129_0]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h0, h2067, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p2129_1]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h7, hlam, p2129_0]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h2066, hlam, p2129_0]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h2069, hlam, p2129_0]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [h2070, hlam, p2129_0]
                          · have p2129_0 := h2129c.1
                            have p2129_1 := h2129c.2.1
                            have p2129_2 := h2129c.2.2.1
                            have p2129_3 := h2129c.2.2.2
                            linarith only [hlam, p2129_0]
                        · linarith only [h2128, hlam, p2071_0]
                      · linarith only [h1157, h2127, hlam]
                    · linarith only [h2126, h8, hlam]
                · linarith only [h0, h2123, hlam]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h2068, hlam, p2071_1]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [h2069, hlam, p2071_0]
              · have p2071_0 := h2071c.1
                have p2071_1 := h2071c.2.1
                have p2071_2 := h2071c.2.2.1
                have p2071_3 := h2071c.2.2.2
                linarith only [hlam, p2071_0]
            · linarith only [h1344, h2, h2066, h2070, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h0, h1344, h2066, h2067, h2069, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1344, h2067, h2068, h8, hc12, hc35, hlam, hphi, ht23]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2185 | h2185
        · linarith only [h0, h1952, h2067, h2185, h3, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2187 | h2187
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2188 | h2188
            · rcases h2bigk with h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c | h2189c
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h2185, h2188, h3, h6, h8, hlam, p2189_2]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                rcases p2189_3 (m.d 0 2) (by simp) with h2192 | h2192
                · rcases p2189_3 (m.d 1 2) (by simp) with h2193 | h2193
                  · linarith only [h0, h2193, hlam]
                  · rcases p2189_3 (m.d 2 3) (by simp) with h2195 | h2195
                    · linarith only [h2195, hlam, p2189_0]
                    · rcases p2189_3 (m.d 2 4) (by simp) with h2197 | h2197
                      · linarith only [h2197, h4, hlam]
                      · linarith only [h2067, h2197, hlam]
                · linarith only [h2192, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                rcases p2189_3 (m.d 0 2) (by simp) with h2201 | h2201
                · rcases p2189_3 (m.d 1 2) (by simp) with h2202 | h2202
                  · linarith only [h0, h2202, hlam]
                  · rcases p2189_3 (m.d 2 3) (by simp) with h2204 | h2204
                    · linarith only [h2204, h3, hlam]
                    · rcases p2189_3 (m.d 2 4) (by simp) with h2206 | h2206
                      · linarith only [h2206, hlam, p2189_0]
                      · rcases p2189_3 (m.d 2 5) (by simp) with h2208 | h2208
                        · linarith only [h2208, h5, hlam]
                        · rcases h4bigk with h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [hlam, p2210_0]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            rcases p2210_3 (m.d 0 4) (by simp) with h2212 | h2212
                            · rcases p2210_3 (m.d 1 4) (by simp) with h2213 | h2213
                              · linarith only [h2, h2213, hlam]
                              · rcases p2210_3 (m.d 2 4) (by simp) with h2215 | h2215
                                · linarith only [h2215, h4, hlam]
                                · linarith only [h1157, h2215, hlam]
                            · linarith only [h2, h2212, hlam]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            rcases p2210_3 (m.d 0 4) (by simp) with h2219 | h2219
                            · rcases p2210_3 (m.d 1 4) (by simp) with h2220 | h2220
                              · linarith only [h2, h2220, hlam]
                              · rcases p2210_3 (m.d 2 4) (by simp) with h2222 | h2222
                                · linarith only [h2222, h4, hlam]
                                · rcases p2210_3 (m.d 3 4) (by simp) with h2224 | h2224
                                  · linarith only [h2224, h6, hlam]
                                  · linarith only [h2067, h2224, hlam]
                            · linarith only [h2219, h4, hlam]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h0, h2067, h3, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2210_1]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            rcases p2210_3 (m.d 0 4) (by simp) with h2229 | h2229
                            · rcases p2210_3 (m.d 1 4) (by simp) with h2230 | h2230
                              · linarith only [h2, h2230, hlam]
                              · linarith only [h2066, h2230, hlam]
                            · linarith only [h2229, hlam, p2210_0]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h2, hlam, p2210_1]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [hlam, p2210_0]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h1157, hlam, p2210_0]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h1344, hlam, p2210_1]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h0, h1157, hc01, hc45, hlam, hphi, ht0b, ht5b, p2189_1, p2210_1]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h4, hlam, p2210_1]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2189_1, p2210_1]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [hlam, p2210_0]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h2067, hlam, p2210_1]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p2189_1, p2210_1]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h6, hlam, p2210_1]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h0, h2066, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p2210_1]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h3, h6, hlam, p2189_2, p2210_1]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [hlam, p2210_0]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            rcases p2210_3 (m.d 0 4) (by simp) with h2248 | h2248
                            · rcases p2210_3 (m.d 1 4) (by simp) with h2249 | h2249
                              · linarith only [h1344, h2249, hlam]
                              · linarith only [h2066, h2249, hlam]
                            · linarith only [h2248, h7, hlam]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h7, hlam, p2210_0]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h2066, hlam, p2210_0]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h2187, hlam, p2210_0]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [h2188, hlam, p2210_0]
                          · have p2210_0 := h2210c.1
                            have p2210_1 := h2210c.2.1
                            have p2210_2 := h2210c.2.2.1
                            have p2210_3 := h2210c.2.2.2
                            linarith only [hlam, p2210_0]
                · linarith only [h2201, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                rcases p2189_3 (m.d 0 2) (by simp) with h2259 | h2259
                · rcases p2189_3 (m.d 1 2) (by simp) with h2260 | h2260
                  · linarith only [h0, h2260, hlam]
                  · rcases p2189_3 (m.d 2 3) (by simp) with h2262 | h2262
                    · linarith only [h2262, h3, hlam]
                    · rcases p2189_3 (m.d 2 4) (by simp) with h2264 | h2264
                      · linarith only [h2264, h4, hlam]
                      · linarith only [h2187, h2264, hlam]
                · linarith only [h2259, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h0, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h8, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h1157, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h1283, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h3, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h2185, hc12, hc35, hlam, hphi, ht23, p2189_1]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h2067, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h2185, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h4, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                rcases p2189_3 (m.d 0 2) (by simp) with h2279 | h2279
                · rcases p2189_3 (m.d 1 2) (by simp) with h2280 | h2280
                  · linarith only [h2280, hlam, p2189_0]
                  · rcases p2189_3 (m.d 2 3) (by simp) with h2282 | h2282
                    · linarith only [h2067, h2282, hlam]
                    · linarith only [h2282, h8, hlam]
                · linarith only [h0, h2279, hlam]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h0, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2189_1]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h0, h2067, h2185, h3, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2189_1]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h5, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                rcases p2189_3 (m.d 0 2) (by simp) with h2290 | h2290
                · rcases p2189_3 (m.d 1 2) (by simp) with h2291 | h2291
                  · linarith only [h2291, hlam, p2189_0]
                  · rcases p2189_3 (m.d 2 3) (by simp) with h2293 | h2293
                    · linarith only [h2185, h2293, hlam]
                    · linarith only [h2293, h8, hlam]
                · linarith only [h0, h2290, hlam]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h8, hc12, hc25, hlam, hphi, p2189_1]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [h2187, hlam, p2189_0]
              · have p2189_0 := h2189c.1
                have p2189_1 := h2189c.2.1
                have p2189_2 := h2189c.2.2.1
                have p2189_3 := h2189c.2.2.2
                linarith only [hlam, p2189_0]
            · linarith only [h1157, h2, h2066, h2067, h2188, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h1157, h2066, h2187, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2302 | h2302
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2303 | h2303
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2304 | h2304
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2305 | h2305
            · linarith only [h0, h2066, h2302, h2305, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1344, h2302, h2304, h2305, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2308 | h2308
            · linarith only [h0, h1157, h2304, h2308, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h2bigk with h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h1344, h2302, h3, h8, hlam, p2310_2]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h1344, h2302, h8, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2310_1]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                rcases p2310_3 (m.d 0 2) (by simp) with h2314 | h2314
                · rcases p2310_3 (m.d 1 2) (by simp) with h2315 | h2315
                  · linarith only [h0, h2315, hlam]
                  · rcases p2310_3 (m.d 2 3) (by simp) with h2317 | h2317
                    · linarith only [h2317, h3, hlam]
                    · linarith only [h2302, h2317, hlam]
                · linarith only [h2314, hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                rcases p2310_3 (m.d 0 2) (by simp) with h2321 | h2321
                · rcases p2310_3 (m.d 1 2) (by simp) with h2322 | h2322
                  · linarith only [h0, h2322, hlam]
                  · rcases p2310_3 (m.d 2 3) (by simp) with h2324 | h2324
                    · linarith only [h2324, h3, hlam]
                    · linarith only [h2303, h2324, hlam]
                · linarith only [h2321, hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h0, hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h8, hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h1157, hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h1283, hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h3, hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                rcases p2310_3 (m.d 0 2) (by simp) with h2334 | h2334
                · rcases p2310_3 (m.d 1 2) (by simp) with h2335 | h2335
                  · linarith only [h2335, hlam, p2310_0]
                  · rcases p2310_3 (m.d 2 3) (by simp) with h2337 | h2337
                    · rcases p2310_3 (m.d 2 4) (by simp) with h2338 | h2338
                      · linarith only [h2302, h2338, hlam]
                      · linarith only [h1157, h2338, hlam]
                    · linarith only [h2337, hlam, p2310_0]
                · linarith only [h0, h2334, hlam]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h1344, h2302, h8, hc12, hc23, hlam, hphi, p2310_1]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h0, h1283, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2310_1]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h4, hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h0, h2304, h3, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2310_1]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h2302, hlam, p2310_1]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h2304, hlam, p2310_1]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h5, hlam, p2310_0]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                rcases p2310_3 (m.d 0 2) (by simp) with h2352 | h2352
                · rcases p2310_3 (m.d 1 2) (by simp) with h2353 | h2353
                  · linarith only [h2353, hlam, p2310_0]
                  · rcases p2310_3 (m.d 2 3) (by simp) with h2355 | h2355
                    · rcases p2310_3 (m.d 2 4) (by simp) with h2356 | h2356
                      · linarith only [h2304, h2356, hlam]
                      · linarith only [h1157, h2356, hlam]
                    · linarith only [h2355, h8, hlam]
                · linarith only [h0, h2352, hlam]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h2303, hlam, p2310_1]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [h0, h1157, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2310_1]
              · have p2310_0 := h2310c.1
                have p2310_1 := h2310c.2.1
                have p2310_2 := h2310c.2.2.1
                have p2310_3 := h2310c.2.2.2
                linarith only [hlam, p2310_0]
        · linarith only [h1344, h2302, h2303, h8, hc12, hc35, hlam, hphi, ht23]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2365 | h2365
        · linarith only [h0, h1952, h2302, h2365, h3, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2367 | h2367
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2368 | h2368
            · rcases h2bigk with h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h2365, h2368, h3, h6, h8, hlam, p2369_2]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                rcases p2369_3 (m.d 0 2) (by simp) with h2372 | h2372
                · rcases p2369_3 (m.d 1 2) (by simp) with h2373 | h2373
                  · linarith only [h0, h2373, hlam]
                  · rcases p2369_3 (m.d 2 3) (by simp) with h2375 | h2375
                    · linarith only [h2375, hlam, p2369_0]
                    · rcases p2369_3 (m.d 2 4) (by simp) with h2377 | h2377
                      · linarith only [h2377, h4, hlam]
                      · linarith only [h2302, h2377, hlam]
                · linarith only [h2372, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h0, h1344, h2066, h2367, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2369_1]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                rcases p2369_3 (m.d 0 2) (by simp) with h2382 | h2382
                · rcases p2369_3 (m.d 1 2) (by simp) with h2383 | h2383
                  · linarith only [h0, h2383, hlam]
                  · rcases p2369_3 (m.d 2 3) (by simp) with h2385 | h2385
                    · linarith only [h2385, h3, hlam]
                    · rcases p2369_3 (m.d 2 4) (by simp) with h2387 | h2387
                      · linarith only [h2387, h4, hlam]
                      · linarith only [h2367, h2387, hlam]
                · linarith only [h2382, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h0, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h8, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h1157, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h1283, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h3, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h2365, h2368, hc12, hc34, hlam, hphi, ht23, p2369_1]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h2302, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h2365, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h4, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                rcases p2369_3 (m.d 0 2) (by simp) with h2402 | h2402
                · rcases p2369_3 (m.d 1 2) (by simp) with h2403 | h2403
                  · linarith only [h2403, hlam, p2369_0]
                  · rcases p2369_3 (m.d 2 3) (by simp) with h2405 | h2405
                    · linarith only [h2302, h2405, hlam]
                    · linarith only [h2405, h8, hlam]
                · linarith only [h0, h2402, hlam]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h8, hc12, hc24, hlam, hphi, p2369_1]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h0, h1283, h2302, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2369_1]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h5, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                rcases p2369_3 (m.d 0 2) (by simp) with h2413 | h2413
                · rcases p2369_3 (m.d 1 2) (by simp) with h2414 | h2414
                  · linarith only [h2414, hlam, p2369_0]
                  · rcases p2369_3 (m.d 2 3) (by simp) with h2416 | h2416
                    · linarith only [h2365, h2416, hlam]
                    · linarith only [h2416, h8, hlam]
                · linarith only [h0, h2413, hlam]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h8, hc12, hc25, hlam, hphi, p2369_1]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [h2367, hlam, p2369_0]
              · have p2369_0 := h2369c.1
                have p2369_1 := h2369c.2.1
                have p2369_2 := h2369c.2.2.1
                have p2369_3 := h2369c.2.2.2
                linarith only [hlam, p2369_0]
            · linarith only [h0, h2302, h2368, h3, h6, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2424 | h2424
            · linarith only [h0, h1157, h2367, h2424, h3, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h0, h2302, h2424, h3, h6, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1157 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1283 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h1344 | h1344
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h1157 h1283 h1344
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h1157 h1283 h1344

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1157 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h1283 | h1283
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h1157 h1283
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h1157 h1283

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h1157 | h1157
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h1157
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h1157

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [h5, hc25, hlam, hphi, ht01, ht12, u0ehi1]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [h3, h4, hc24, hlam, hphi, ht01, ht12, u0ehi2]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [h2, hc14, hlam, hphi, ht01, u0ehi0]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0 m hb0 hb2 hb4 h0 h1
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x1 m hb0 hb2 hb4 h0 h1

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_H_R_L_I_L_I_x1 m hb0 hb2 hb4 h0

end R2N4
