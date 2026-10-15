import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6334000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1951 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1952 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h1953 | h1953
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1954 | h1954
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1955 | h1955
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1956 | h1956
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1957 | h1957
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1958 | h1958
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1959 | h1959
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1960 | h1960
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1961 | h1961
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1962 | h1962
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1963 | h1963
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1964 | h1964
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1965 | h1965
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1966 | h1966
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1967 | h1967
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1968 | h1968
                                · linarith only [h1951, h1960, h1965, h1968, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h0, h1951, h1961, h1963, h1967, h1968, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1971 | h1971
                                · linarith only [h0, h1951, h1957, h1967, h1971, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
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
                                    linarith only [h0, h1951, h1960, h1966, hc35, hlam, hphi, ht0b, ht5b, p1973_1, u0elo1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h0, h1959, h1967, hc25, hlam, hphi, ht0b, ht5b, p1973_1, u0elo1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h0, h1959, h1965, h1967, hc34, hlam, hphi, ht0b, ht45, ht5b, p1973_1, u0elo1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1952, hc14, hlam, hphi, ht0b, ht45, ht5b, p1973_1, u0elo1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [hlam, p1973_0]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1957, h1959, h1965, h1967, hc34, hlam, hphi, ht0b, ht45, ht5b, p1973_1, u0elo1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1959, h1965, h1967, hc34, hlam, hphi, ht0b, ht45, ht5b, p1973_1, u0elo1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1959, h1965, h1967, hc34, hlam, hphi, ht0b, ht45, ht5b, p1973_1, u0elo1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1951, hlam, p1973_1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1954, hlam, p1973_1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [hlam, p1973_0]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1951, h1959, h1965, h1967, hc34, hlam, hphi, ht0b, ht45, ht5b, p1973_1, u0elo0]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h0, h1951, h1959, h1965, h1967, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1973_1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1952, hlam, p1973_0]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1955, hlam, p1973_0]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1957, hlam, p1973_0]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [hlam, p1973_0]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1959, h1965, h1967, hc34, hlam, hphi, ht0b, ht45, ht5b, p1973_1, u0elo3]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1953, hlam, p1973_0]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1956, hlam, p1973_1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1958, hlam, p1973_0]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [h1959, hlam, p1973_1]
                                  · have p1973_0 := h1973c.1
                                    have p1973_1 := h1973c.2.1
                                    have p1973_2 := h1973c.2.2.1
                                    have p1973_3 := h1973c.2.2.2
                                    linarith only [hlam, p1973_0]
                            · linarith only [h1965, h1966, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h0, h1951, h1963, h1965, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h1951, h1958, h1963, h1964, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2002 | h2002
                        · linarith only [h0, h1951, h1957, h1963, h2002, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2004 | h2004
                          · linarith only [h1954, h1963, h2004, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2006 | h2006
                            · linarith only [h1960, h2002, h2006, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2008 | h2008
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2009 | h2009
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
                                    linarith only [h0, hlam, p2010_1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h0, h1957, h1960, h2002, h2009, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2010_1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h0, h1952, h1961, h2008, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2010_1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h0, h1958, h1960, h2002, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2010_1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1951, h1960, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2010_1, u0elo1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [hlam, p2010_0]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1957, h1960, h2002, h2009, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2010_1, u0elo1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1952, h1961, h2008, hc45, hlam, hphi, ht0b, ht5b, p2010_1, u0elo1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1958, h1960, h2002, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2010_1, u0elo1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1951, hlam, p2010_1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1954, hlam, p2010_1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [hlam, p2010_0]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1951, h1952, h1961, h2008, hc45, hlam, hphi, ht0b, ht5b, p2010_1, u0elo0]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h0, h1951, h1958, h1960, h2002, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2010_1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1952, hlam, p2010_0]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1955, hlam, p2010_0]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1957, hlam, p2010_0]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [hlam, p2010_0]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1958, h1960, h2002, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2010_1, u0elo3]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1953, hlam, p2010_0]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1956, hlam, p2010_1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1958, hlam, p2010_0]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [h1959, hlam, p2010_1]
                                  · have p2010_0 := h2010c.1
                                    have p2010_1 := h2010c.2.1
                                    have p2010_2 := h2010c.2.2.1
                                    have p2010_3 := h2010c.2.2.2
                                    linarith only [hlam, p2010_0]
                                · linarith only [h0, h1952, h1961, h2008, h2009, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2037 | h2037
                                · linarith only [h0, h1951, h1957, h2004, h2008, h2037, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · linarith only [h0, h1951, h1957, h1959, h1960, h1963, h2037, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1962, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1955, h1961, hlam]
                · linarith only [h0, h1954, h1960, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2043 | h2043
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2044 | h2044
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2045 | h2045
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2046 | h2046
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2047 | h2047
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2048 | h2048
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2049 | h2049
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2050 | h2050
                              · linarith only [h1952, h1959, h2044, h2050, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2052 | h2052
                                · linarith only [h1951, h1959, h2043, h2048, h2052, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases h0bigk with h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [hlam, p2054_0]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h0, hlam, p2054_1]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h0, h1951, h2043, h2049, h2052, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2054_1]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    rcases p2054_3 (m.d 0 1) (by simp) with h2058 | h2058
                                    · rcases p2054_3 (m.d 0 2) (by simp) with h2059 | h2059
                                      · rcases p2054_3 (m.d 0 3) (by simp) with h2060 | h2060
                                        · linarith only [h1951, h2060, hlam]
                                        · linarith only [h1957, h2060, hlam]
                                      · linarith only [h1955, h2059, hlam]
                                    · linarith only [h1952, h2058, hlam]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    rcases p2054_3 (m.d 0 1) (by simp) with h2065 | h2065
                                    · rcases p2054_3 (m.d 0 2) (by simp) with h2066 | h2066
                                      · rcases p2054_3 (m.d 0 3) (by simp) with h2067 | h2067
                                        · linarith only [h1951, h2067, hlam]
                                        · linarith only [h1958, h2067, hlam]
                                      · linarith only [h1956, h2066, hlam]
                                    · linarith only [h1953, h2065, hlam]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1951, h2043, h2049, h2052, hc34, hlam, hphi, ht0b, ht45, ht5b, p2054_1, u0elo1]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [hlam, p2054_0]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1951, h2043, h2049, h2052, hc34, hlam, hphi, ht0b, ht45, ht5b, p2054_1, u0elo1]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    rcases p2054_3 (m.d 0 1) (by simp) with h2075 | h2075
                                    · linarith only [h0, h2075, hlam]
                                    · linarith only [h1952, h2075, hlam]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    rcases p2054_3 (m.d 0 1) (by simp) with h2078 | h2078
                                    · linarith only [h0, h2078, hlam]
                                    · linarith only [h1953, h2078, hlam]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1951, hlam, p2054_1]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1954, hlam, p2054_1]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [hlam, p2054_0]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    rcases p2054_3 (m.d 0 1) (by simp) with h2084 | h2084
                                    · rcases p2054_3 (m.d 0 2) (by simp) with h2085 | h2085
                                      · rcases p2054_3 (m.d 0 3) (by simp) with h2086 | h2086
                                        · rcases p2054_3 (m.d 0 4) (by simp) with h2087 | h2087
                                          · linarith only [h1957, h2087, hlam]
                                          · rcases p2054_3 (m.d 0 5) (by simp) with h2089 | h2089
                                            · linarith only [h1958, h2089, hlam]
                                            · linarith only [h1959, h2089, hlam]
                                        · linarith only [h1957, h2086, hlam]
                                      · linarith only [h1955, h2085, hlam]
                                    · linarith only [h1952, h2084, hlam]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    rcases p2054_3 (m.d 0 1) (by simp) with h2095 | h2095
                                    · rcases p2054_3 (m.d 0 2) (by simp) with h2096 | h2096
                                      · rcases p2054_3 (m.d 0 3) (by simp) with h2097 | h2097
                                        · rcases p2054_3 (m.d 0 4) (by simp) with h2098 | h2098
                                          · linarith only [h1957, h2098, hlam]
                                          · rcases p2054_3 (m.d 0 5) (by simp) with h2100 | h2100
                                            · linarith only [h1958, h2100, hlam]
                                            · rcases h2bigk with h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h0, hlam, p2102_1]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h2049, h2052, hc34, hlam, hphi, ht0b, ht45, ht5b, p2102_1, u0elo1]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                rcases p2102_3 (m.d 0 2) (by simp) with h2106 | h2106
                                                · rcases p2102_3 (m.d 1 2) (by simp) with h2107 | h2107
                                                  · rcases p2102_3 (m.d 2 3) (by simp) with h2108 | h2108
                                                    · linarith only [h1954, h2108, hlam]
                                                    · linarith only [h2048, h2108, hlam]
                                                  · linarith only [h2044, h2107, hlam]
                                                · linarith only [h2106, hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                rcases p2102_3 (m.d 0 2) (by simp) with h2113 | h2113
                                                · rcases p2102_3 (m.d 1 2) (by simp) with h2114 | h2114
                                                  · rcases p2102_3 (m.d 2 3) (by simp) with h2115 | h2115
                                                    · linarith only [h1954, h2115, hlam]
                                                    · linarith only [h2049, h2115, hlam]
                                                  · linarith only [h2045, h2114, hlam]
                                                · linarith only [h2113, hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h0, h1951, h1952, h1959, h2044, h2048, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2054_1, p2102_1]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                rcases p2102_3 (m.d 0 2) (by simp) with h2122 | h2122
                                                · linarith only [h0, h2122, hlam]
                                                · linarith only [h1954, h2122, hlam]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h0, h1951, h1952, h1959, h2044, hlam, p2054_1, p2102_2]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h0, h1951, h1953, h2045, hlam, p2054_1, p2102_2]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h1954, hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h2043, hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h1951, h2043, h2048, hc34, hlam, hphi, ht0b, ht45, ht5b, p2102_1, u0elo0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h0, h1951, h2043, hc25, hlam, hphi, ht0b, ht5b, p2102_1, u0elo1]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h1955, hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h2044, hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h2048, hlam, p2102_1]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h2050, hlam, p2102_1]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h1956, hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h2045, hlam, p2102_0]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h2049, hlam, p2102_1]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [h2048, hc34, hlam, hphi, ht45, p2102_1, u5elo2]
                                              · have p2102_0 := h2102c.1
                                                have p2102_1 := h2102c.2.1
                                                have p2102_2 := h2102c.2.2.1
                                                have p2102_3 := h2102c.2.2.2
                                                linarith only [hlam, p2102_0]
                                        · linarith only [h1958, h2097, hlam]
                                      · linarith only [h1956, h2096, hlam]
                                    · linarith only [h1953, h2095, hlam]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1952, hlam, p2054_0]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1955, hlam, p2054_0]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1957, hlam, p2054_0]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [hlam, p2054_0]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1959, hlam, p2054_0]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1953, hlam, p2054_0]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1956, hlam, p2054_1]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1958, hlam, p2054_0]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [h1952, h2044, h2048, hc34, hlam, hphi, ht45, p2054_1, u5elo0]
                                  · have p2054_0 := h2054c.1
                                    have p2054_1 := h2054c.2.1
                                    have p2054_2 := h2054c.2.2.1
                                    have p2054_3 := h2054c.2.2.2
                                    linarith only [hlam, p2054_0]
                            · linarith only [h0, h1951, h2047, h2049, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h1957, h1959, h2048, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h0, h1951, h1958, h2046, h2047, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h1957, h1959, h2046, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h2045, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1955, h2044, hlam]
                · linarith only [h0, h1954, h2043, hlam]
            · linarith only [h1957, h1958, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2163 | h2163
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2164 | h2164
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2165 | h2165
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2166 | h2166
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2167 | h2167
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2168 | h2168
                      · linarith only [h1951, h1957, h2163, h2168, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2170 | h2170
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2171 | h2171
                          · linarith only [h1951, h1957, h2165, h2171, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2173 | h2173
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2174 | h2174
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2175 | h2175
                                · rcases h0bigk with h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c | h2176c
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [hlam, p2176_0]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h0, hlam, p2176_1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h0, h1951, h2165, h2173, h2175, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2176_1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h0, h1951, h1957, h2165, h2173, h2175, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2176_1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    rcases p2176_3 (m.d 0 1) (by simp) with h2181 | h2181
                                    · rcases p2176_3 (m.d 0 2) (by simp) with h2182 | h2182
                                      · rcases p2176_3 (m.d 0 3) (by simp) with h2183 | h2183
                                        · linarith only [h1951, h2183, hlam]
                                        · linarith only [h2163, h2183, hlam]
                                      · linarith only [h1956, h2182, hlam]
                                    · linarith only [h1953, h2181, hlam]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h1951, h2165, h2173, h2175, hc45, hlam, hphi, ht0b, ht5b, p2176_1, u0elo1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [hlam, p2176_0]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h1951, h2165, h2173, h2175, hc45, hlam, hphi, ht0b, ht5b, p2176_1, u0elo1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h1951, h1957, h2165, h2173, h2175, hc45, hlam, hphi, ht0b, ht5b, p2176_1, u0elo1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    rcases p2176_3 (m.d 0 1) (by simp) with h2192 | h2192
                                    · linarith only [h0, h2192, hlam]
                                    · linarith only [h1953, h2192, hlam]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h1951, hlam, p2176_1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h1954, hlam, p2176_1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [hlam, p2176_0]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h1957, hlam, p2176_1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    rcases p2176_3 (m.d 0 1) (by simp) with h2199 | h2199
                                    · rcases p2176_3 (m.d 0 2) (by simp) with h2200 | h2200
                                      · rcases p2176_3 (m.d 0 3) (by simp) with h2201 | h2201
                                        · rcases p2176_3 (m.d 0 4) (by simp) with h2202 | h2202
                                          · rcases p2176_3 (m.d 0 5) (by simp) with h2203 | h2203
                                            · linarith only [h2163, h2203, hlam]
                                            · rcases h2bigk with h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c | h2205c
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h0, hlam, p2205_1]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h2173, h2175, hc45, hlam, hphi, ht0b, ht5b, p2205_1, u0elo1]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h2171, h2173, h2175, hc45, hlam, hphi, ht0b, ht5b, p2205_1, u0elo1]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                rcases p2205_3 (m.d 0 2) (by simp) with h2210 | h2210
                                                · rcases p2205_3 (m.d 1 2) (by simp) with h2211 | h2211
                                                  · rcases p2205_3 (m.d 2 3) (by simp) with h2212 | h2212
                                                    · linarith only [h1954, h2212, hlam]
                                                    · linarith only [h2173, h2212, hlam]
                                                  · linarith only [h2167, h2211, hlam]
                                                · linarith only [h2210, hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h0, h1952, h1953, h1957, h2167, h2173, h2175, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2176_1, p2205_1]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                rcases p2205_3 (m.d 0 2) (by simp) with h2219 | h2219
                                                · linarith only [h0, h2219, hlam]
                                                · linarith only [h1954, h2219, hlam]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                rcases p2205_3 (m.d 0 2) (by simp) with h2222 | h2222
                                                · linarith only [h0, h2222, hlam]
                                                · linarith only [h1955, h2222, hlam]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h0, h1952, h1953, h1957, h2167, hlam, p2176_1, p2205_2]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h1954, hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h2165, hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h2171, hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h1951, h2165, h2173, h2175, hc45, hlam, hphi, ht0b, ht5b, p2205_1, u0elo0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h1955, hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h2166, hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h1953, h1955, h1957, h2167, h2173, h2175, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p2176_1, p2205_1, u0elo1]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h0, h1952, h2166, h2173, h2175, hc45, hlam, hphi, ht0b, ht5b, p2205_1, u0elo1]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h1956, hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h2167, hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h2173, hlam, p2205_1]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [h2174, hlam, p2205_0]
                                              · have p2205_0 := h2205c.1
                                                have p2205_1 := h2205c.2.1
                                                have p2205_2 := h2205c.2.2.1
                                                have p2205_3 := h2205c.2.2.2
                                                linarith only [hlam, p2205_0]
                                          · linarith only [h2164, h2202, hlam]
                                        · linarith only [h2163, h2201, hlam]
                                      · linarith only [h1956, h2200, hlam]
                                    · linarith only [h1953, h2199, hlam]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h1952, hlam, p2176_0]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h1955, hlam, p2176_0]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h0, h1952, h1954, h2173, h2175, hc45, hlam, hphi, ht0b, ht5b, p2176_1, u0elo1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [hlam, p2176_0]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    rcases p2176_3 (m.d 0 1) (by simp) with h2249 | h2249
                                    · rcases p2176_3 (m.d 0 2) (by simp) with h2250 | h2250
                                      · rcases p2176_3 (m.d 0 3) (by simp) with h2251 | h2251
                                        · linarith only [h1957, h2251, hlam]
                                        · linarith only [h2163, h2251, hlam]
                                      · linarith only [h1956, h2250, hlam]
                                    · linarith only [h1953, h2249, hlam]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h1953, hlam, p2176_0]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h1956, hlam, p2176_1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h2163, hlam, p2176_0]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [h2164, hlam, p2176_1]
                                  · have p2176_0 := h2176c.1
                                    have p2176_1 := h2176c.2.1
                                    have p2176_2 := h2176c.2.2.1
                                    have p2176_3 := h2176c.2.2.2
                                    linarith only [hlam, p2176_0]
                                · linarith only [h1951, h1957, h2165, h2173, h2175, hc35, hlam, hphi, u5elo4]
                              · linarith only [h2164, h2171, h2173, h2174, hc35, hlam, hphi, u5elo0]
                            · linarith only [h1957, h2163, h2173, hc23, hc34, hlam, hphi]
                        · linarith only [h1957, h2163, h2170, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h2167, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1951, h1955, h2165, h2166, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h1954, h2165, hlam]
              · linarith only [h1957, h2163, h2164, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2269 | h2269
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2270 | h2270
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2271 | h2271
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2272 | h2272
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2273 | h2273
                      · linarith only [h1951, h1957, h2273, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2275 | h2275
                        · linarith only [h1951, h2163, h2275, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2277 | h2277
                          · linarith only [h1951, h1957, h2270, h2277, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2279 | h2279
                            · linarith only [h1951, h2163, h2270, h2279, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2281 | h2281
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2282 | h2282
                                · rcases h0bigk with h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c | h2283c
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [hlam, p2283_0]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h0, hlam, p2283_1]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    rcases p2283_3 (m.d 0 1) (by simp) with h2286 | h2286
                                    · rcases p2283_3 (m.d 0 2) (by simp) with h2287 | h2287
                                      · rcases p2283_3 (m.d 0 3) (by simp) with h2288 | h2288
                                        · linarith only [h1951, h2288, hlam]
                                        · rcases p2283_3 (m.d 0 4) (by simp) with h2290 | h2290
                                          · linarith only [h1952, h2290, hlam]
                                          · linarith only [h1957, h2290, hlam]
                                      · linarith only [h1954, h2287, hlam]
                                    · linarith only [h1951, h2286, hlam]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h0, h1952, h2271, h2281, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2283_1]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    rcases p2283_3 (m.d 0 1) (by simp) with h2296 | h2296
                                    · rcases p2283_3 (m.d 0 2) (by simp) with h2297 | h2297
                                      · rcases p2283_3 (m.d 0 3) (by simp) with h2298 | h2298
                                        · linarith only [h1951, h2298, hlam]
                                        · rcases p2283_3 (m.d 0 4) (by simp) with h2300 | h2300
                                          · linarith only [h1952, h2300, hlam]
                                          · linarith only [h2269, h2300, hlam]
                                      · linarith only [h1956, h2297, hlam]
                                    · linarith only [h1953, h2296, hlam]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h1951, h2270, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2283_1, u0elo1]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [hlam, p2283_0]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    rcases p2283_3 (m.d 0 1) (by simp) with h2307 | h2307
                                    · linarith only [h0, h2307, hlam]
                                    · linarith only [h1951, h2307, hlam]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h1952, h2271, h2281, hc45, hlam, hphi, ht0b, ht5b, p2283_1, u0elo1]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    rcases p2283_3 (m.d 0 1) (by simp) with h2311 | h2311
                                    · linarith only [h0, h2311, hlam]
                                    · linarith only [h1953, h2311, hlam]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h1951, hlam, p2283_1]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h1954, hlam, p2283_1]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [hlam, p2283_0]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h1957, hlam, p2283_1]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h2163, hlam, p2283_1]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h1952, hlam, p2283_0]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h1955, hlam, p2283_0]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    rcases p2283_3 (m.d 0 1) (by simp) with h2321 | h2321
                                    · rcases p2283_3 (m.d 0 2) (by simp) with h2322 | h2322
                                      · rcases p2283_3 (m.d 0 3) (by simp) with h2323 | h2323
                                        · linarith only [h1957, h2323, hlam]
                                        · rcases p2283_3 (m.d 0 4) (by simp) with h2325 | h2325
                                          · rcases p2283_3 (m.d 0 5) (by simp) with h2326 | h2326
                                            · linarith only [h2269, h2326, hlam]
                                            · linarith only [h2163, h2326, hlam]
                                          · linarith only [h1957, h2325, hlam]
                                      · linarith only [h1954, h2322, hlam]
                                    · linarith only [h1951, h2321, hlam]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [hlam, p2283_0]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    rcases p2283_3 (m.d 0 1) (by simp) with h2333 | h2333
                                    · rcases p2283_3 (m.d 0 2) (by simp) with h2334 | h2334
                                      · rcases p2283_3 (m.d 0 3) (by simp) with h2335 | h2335
                                        · linarith only [h1957, h2335, hlam]
                                        · rcases p2283_3 (m.d 0 4) (by simp) with h2337 | h2337
                                          · rcases p2283_3 (m.d 0 5) (by simp) with h2338 | h2338
                                            · linarith only [h2269, h2338, hlam]
                                            · rcases h2bigk with h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h0, hlam, p2340_1]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                rcases p2340_3 (m.d 0 2) (by simp) with h2343 | h2343
                                                · rcases p2340_3 (m.d 1 2) (by simp) with h2344 | h2344
                                                  · rcases p2340_3 (m.d 2 3) (by simp) with h2345 | h2345
                                                    · linarith only [h2345, hlam, p2340_0]
                                                    · rcases p2340_3 (m.d 2 4) (by simp) with h2347 | h2347
                                                      · linarith only [h1955, h2347, hlam]
                                                      · linarith only [h2277, h2347, hlam]
                                                  · linarith only [h2270, h2344, hlam]
                                                · linarith only [h2343, hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h2281, hc45, hlam, hphi, ht0b, ht5b, p2340_1, u0elo1]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                rcases p2340_3 (m.d 0 2) (by simp) with h2353 | h2353
                                                · rcases p2340_3 (m.d 1 2) (by simp) with h2354 | h2354
                                                  · rcases p2340_3 (m.d 2 3) (by simp) with h2355 | h2355
                                                    · linarith only [h1954, h2355, hlam]
                                                    · rcases p2340_3 (m.d 2 4) (by simp) with h2357 | h2357
                                                      · linarith only [h1955, h2357, hlam]
                                                      · linarith only [h2281, h2357, hlam]
                                                  · linarith only [h2272, h2354, hlam]
                                                · linarith only [h2353, hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h0, h1951, h1952, h2163, h2270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2283_1, p2340_1]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h0, h1951, h1952, h2163, h2270, hlam, p2283_1, p2340_2]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                rcases p2340_3 (m.d 0 2) (by simp) with h2365 | h2365
                                                · linarith only [h0, h2365, hlam]
                                                · linarith only [h1955, h2365, hlam]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h0, h1952, h1953, h2272, hlam, p2283_1, p2340_2]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h1954, hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h2270, hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h2277, hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h2279, hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h1955, hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h2271, hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h1952, h2271, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2340_1, u0elo0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h0, h1952, h2271, hc25, hlam, hphi, ht0b, ht5b, p2340_1, u0elo1]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h1956, hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h2272, hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [hc23, hlam, hphi, ht34, ht45, p2340_1, u5elo2]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [h2281, hlam, p2340_0]
                                              · have p2340_0 := h2340c.1
                                                have p2340_1 := h2340c.2.1
                                                have p2340_2 := h2340c.2.2.1
                                                have p2340_3 := h2340c.2.2.2
                                                linarith only [hlam, p2340_0]
                                          · linarith only [h2269, h2337, hlam]
                                      · linarith only [h1956, h2334, hlam]
                                    · linarith only [h1953, h2333, hlam]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h1953, hlam, p2283_0]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h1956, hlam, p2283_1]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h1951, h2270, hc23, hlam, hphi, ht34, ht45, p2283_1, u5elo0]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [h2269, hlam, p2283_1]
                                  · have p2283_0 := h2283c.1
                                    have p2283_1 := h2283c.2.1
                                    have p2283_2 := h2283c.2.2.1
                                    have p2283_3 := h2283c.2.2.2
                                    linarith only [hlam, p2283_0]
                                · linarith only [h1951, h1957, h2270, h2282, hc23, hlam, hphi, ht34, ht45, u5elo4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2393 | h2393
                                · rcases h0bigk with h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [hlam, p2394_0]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h0, hlam, p2394_1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    rcases p2394_3 (m.d 0 1) (by simp) with h2397 | h2397
                                    · rcases p2394_3 (m.d 0 2) (by simp) with h2398 | h2398
                                      · rcases p2394_3 (m.d 0 3) (by simp) with h2399 | h2399
                                        · linarith only [h1951, h2399, hlam]
                                        · rcases p2394_3 (m.d 0 4) (by simp) with h2401 | h2401
                                          · linarith only [h1952, h2401, hlam]
                                          · linarith only [h1957, h2401, hlam]
                                      · linarith only [h1954, h2398, hlam]
                                    · linarith only [h1951, h2397, hlam]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h0, h2269, h2277, h2281, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2394_1, u0elo1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h0, h2269, h2277, h2281, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2394_1, u0elo1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h1951, h2270, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2394_1, u0elo1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [hlam, p2394_0]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    rcases p2394_3 (m.d 0 1) (by simp) with h2410 | h2410
                                    · linarith only [h0, h2410, hlam]
                                    · linarith only [h1951, h2410, hlam]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h2269, h2277, h2281, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2394_1, u0elo1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h2269, h2277, h2281, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2394_1, u0elo1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h1951, hlam, p2394_1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h1954, hlam, p2394_1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [hlam, p2394_0]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h1957, hlam, p2394_1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h2163, hlam, p2394_1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h1952, hlam, p2394_0]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h1955, hlam, p2394_0]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    rcases p2394_3 (m.d 0 1) (by simp) with h2422 | h2422
                                    · rcases p2394_3 (m.d 0 2) (by simp) with h2423 | h2423
                                      · rcases p2394_3 (m.d 0 3) (by simp) with h2424 | h2424
                                        · linarith only [h1957, h2424, hlam]
                                        · rcases p2394_3 (m.d 0 4) (by simp) with h2426 | h2426
                                          · rcases p2394_3 (m.d 0 5) (by simp) with h2427 | h2427
                                            · linarith only [h2269, h2427, hlam]
                                            · linarith only [h2163, h2427, hlam]
                                          · linarith only [h1957, h2426, hlam]
                                      · linarith only [h1954, h2423, hlam]
                                    · linarith only [h1951, h2422, hlam]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [hlam, p2394_0]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h1952, h2269, h2277, h2281, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2394_1, u0elo0]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h1953, hlam, p2394_0]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h1956, hlam, p2394_1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h1951, h2270, hc23, hlam, hphi, ht34, ht45, p2394_1, u5elo0]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [h2269, hlam, p2394_1]
                                  · have p2394_0 := h2394c.1
                                    have p2394_1 := h2394c.2.1
                                    have p2394_2 := h2394c.2.2.1
                                    have p2394_3 := h2394c.2.2.2
                                    linarith only [hlam, p2394_0]
                                · linarith only [h1951, h1957, h2270, h2393, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h2272, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1955, h2271, hlam]
                · linarith only [h0, h1954, h2270, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2444 | h2444
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2445 | h2445
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2446 | h2446
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2447 | h2447
                      · linarith only [h1951, h1957, h2447, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2449 | h2449
                        · linarith only [h1951, h1957, h2269, h2449, hc35, hlam, hphi, u5elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2451 | h2451
                          · linarith only [h1951, h1957, h2269, h2444, h2451, hc34, hlam, hphi, ht45, u5elo4]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2453 | h2453
                            · linarith only [h1951, h1957, h2163, h2269, h2444, h2453, hc05, hlam, hphi, u5elo4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2455 | h2455
                              · linarith only [h1952, h2269, h2445, h2455, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2457 | h2457
                                · rcases h0bigk with h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c | h2458c
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [hlam, p2458_0]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h0, hlam, p2458_1]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    rcases p2458_3 (m.d 0 1) (by simp) with h2461 | h2461
                                    · rcases p2458_3 (m.d 0 2) (by simp) with h2462 | h2462
                                      · rcases p2458_3 (m.d 0 3) (by simp) with h2463 | h2463
                                        · linarith only [h1951, h2463, hlam]
                                        · rcases p2458_3 (m.d 0 4) (by simp) with h2465 | h2465
                                          · linarith only [h1952, h2465, hlam]
                                          · linarith only [h1957, h2465, hlam]
                                      · linarith only [h1954, h2462, hlam]
                                    · linarith only [h1951, h2461, hlam]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    rcases p2458_3 (m.d 0 1) (by simp) with h2470 | h2470
                                    · rcases p2458_3 (m.d 0 2) (by simp) with h2471 | h2471
                                      · rcases p2458_3 (m.d 0 3) (by simp) with h2472 | h2472
                                        · linarith only [h1951, h2472, hlam]
                                        · rcases p2458_3 (m.d 0 4) (by simp) with h2474 | h2474
                                          · linarith only [h1952, h2474, hlam]
                                          · rcases p2458_3 (m.d 0 5) (by simp) with h2476 | h2476
                                            · linarith only [h1953, h2476, hlam]
                                            · linarith only [h2269, h2476, hlam]
                                      · linarith only [h1955, h2471, hlam]
                                    · linarith only [h1952, h2470, hlam]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    rcases p2458_3 (m.d 0 1) (by simp) with h2481 | h2481
                                    · rcases p2458_3 (m.d 0 2) (by simp) with h2482 | h2482
                                      · rcases p2458_3 (m.d 0 3) (by simp) with h2483 | h2483
                                        · linarith only [h1951, h2483, hlam]
                                        · rcases p2458_3 (m.d 0 4) (by simp) with h2485 | h2485
                                          · linarith only [h1952, h2485, hlam]
                                          · rcases p2458_3 (m.d 0 5) (by simp) with h2487 | h2487
                                            · linarith only [h1953, h2487, hlam]
                                            · rcases h2bigk with h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c | h2489c
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h0, hlam, p2489_1]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                rcases p2489_3 (m.d 0 2) (by simp) with h2492 | h2492
                                                · rcases p2489_3 (m.d 1 2) (by simp) with h2493 | h2493
                                                  · rcases p2489_3 (m.d 2 3) (by simp) with h2494 | h2494
                                                    · linarith only [h2494, hlam, p2489_0]
                                                    · rcases p2489_3 (m.d 2 4) (by simp) with h2496 | h2496
                                                      · linarith only [h1955, h2496, hlam]
                                                      · linarith only [h2451, h2496, hlam]
                                                  · linarith only [h2444, h2493, hlam]
                                                · linarith only [h2492, hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                rcases p2489_3 (m.d 0 2) (by simp) with h2501 | h2501
                                                · rcases p2489_3 (m.d 1 2) (by simp) with h2502 | h2502
                                                  · rcases p2489_3 (m.d 2 3) (by simp) with h2503 | h2503
                                                    · linarith only [h1954, h2503, hlam]
                                                    · rcases p2489_3 (m.d 2 4) (by simp) with h2505 | h2505
                                                      · linarith only [h2505, hlam, p2489_0]
                                                      · rcases p2489_3 (m.d 2 5) (by simp) with h2507 | h2507
                                                        · linarith only [h1956, h2507, hlam]
                                                        · linarith only [h2455, h2507, hlam]
                                                  · linarith only [h2445, h2502, hlam]
                                                · linarith only [h2501, hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                rcases p2489_3 (m.d 0 2) (by simp) with h2512 | h2512
                                                · rcases p2489_3 (m.d 1 2) (by simp) with h2513 | h2513
                                                  · rcases p2489_3 (m.d 2 3) (by simp) with h2514 | h2514
                                                    · linarith only [h1954, h2514, hlam]
                                                    · rcases p2489_3 (m.d 2 4) (by simp) with h2516 | h2516
                                                      · linarith only [h1955, h2516, hlam]
                                                      · rcases p2489_3 (m.d 2 5) (by simp) with h2518 | h2518
                                                        · linarith only [h2518, hlam, p2489_0]
                                                        · rcases h2emin with h2520 | h2520 | h2520 | h2520 | h2520
                                                          · rcases h3bigk with h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c | h2521c
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h0, h1957, h2269, h2444, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2458_1, p2521_1]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h0, h1957, h2269, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2458_1, p2521_1]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h1957, hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h2163, hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h1951, hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h0, h1951, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2521_1]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h2447, hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h2449, hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h1954, hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h2444, hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h2451, hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h2453, hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              rcases p2521_3 (m.d 0 3) (by simp) with h2537 | h2537
                                                              · linarith only [h2537, hlam, p2521_0]
                                                              · rcases p2521_3 (m.d 1 3) (by simp) with h2539 | h2539
                                                                · linarith only [h2447, h2539, hlam]
                                                                · rcases p2521_3 (m.d 2 3) (by simp) with h2541 | h2541
                                                                  · linarith only [h2451, h2541, hlam]
                                                                  · rcases p2521_3 (m.d 3 4) (by simp) with h2543 | h2543
                                                                    · rcases p2521_3 (m.d 3 5) (by simp) with h2544 | h2544
                                                                      · linarith only [h2457, h2544, hlam]
                                                                      · linarith only [h2163, h2544, hlam]
                                                                    · linarith only [h2543, hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              rcases p2521_3 (m.d 0 3) (by simp) with h2548 | h2548
                                                              · linarith only [h1957, h2548, hlam]
                                                              · linarith only [h1951, h2548, hlam]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              rcases p2521_3 (m.d 0 3) (by simp) with h2551 | h2551
                                                              · linarith only [h1957, h2551, hlam]
                                                              · linarith only [h1954, h2551, hlam]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h1957, h2269, h2457, hc03, hc34, hlam, hphi, p2521_1]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h1951, hc13, hlam, hphi, ht34, ht45, p2521_1, u5elo3]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h2444, hc23, hlam, hphi, ht34, ht45, p2521_1, u5elo3]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [hc23, hlam, hphi, ht34, ht45, p2521_1, u5elo3]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [h2457, hlam, p2521_0]
                                                            · have p2521_0 := h2521c.1
                                                              have p2521_1 := h2521c.2.1
                                                              have p2521_2 := h2521c.2.2.1
                                                              have p2521_3 := h2521c.2.2.2
                                                              linarith only [hlam, p2521_0]
                                                          · rcases h3bigk with h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c | h2561c
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h0, h1957, h2269, h2444, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2458_1, p2561_1]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h0, h1957, h2269, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2458_1, p2561_1]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h1957, hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h2163, hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h1951, hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h0, h1951, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2561_1]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h2447, hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h2449, hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h1954, hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h2444, hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h2451, hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h2453, hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              rcases p2561_3 (m.d 0 3) (by simp) with h2577 | h2577
                                                              · linarith only [h2577, hlam, p2561_0]
                                                              · rcases p2561_3 (m.d 1 3) (by simp) with h2579 | h2579
                                                                · linarith only [h2447, h2579, hlam]
                                                                · rcases p2561_3 (m.d 2 3) (by simp) with h2581 | h2581
                                                                  · linarith only [h2451, h2581, hlam]
                                                                  · rcases p2561_3 (m.d 3 4) (by simp) with h2583 | h2583
                                                                    · rcases p2561_3 (m.d 3 5) (by simp) with h2584 | h2584
                                                                      · linarith only [h2457, h2584, hlam]
                                                                      · linarith only [h2163, h2584, hlam]
                                                                    · linarith only [h2583, hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              rcases p2561_3 (m.d 0 3) (by simp) with h2588 | h2588
                                                              · linarith only [h1957, h2588, hlam]
                                                              · linarith only [h1951, h2588, hlam]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              rcases p2561_3 (m.d 0 3) (by simp) with h2591 | h2591
                                                              · linarith only [h1957, h2591, hlam]
                                                              · linarith only [h1954, h2591, hlam]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h2163, hc03, hc34, hlam, hphi, p2561_1]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h1951, hc13, hlam, hphi, ht34, ht45, p2561_1, u5elo3]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h2444, hc23, hlam, hphi, ht34, ht45, p2561_1, u5elo3]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [hc23, hlam, hphi, ht34, ht45, p2561_1, u5elo3]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [h2457, hlam, p2561_0]
                                                            · have p2561_0 := h2561c.1
                                                              have p2561_1 := h2561c.2.1
                                                              have p2561_2 := h2561c.2.2.1
                                                              have p2561_3 := h2561c.2.2.2
                                                              linarith only [hlam, p2561_0]
                                                          · linarith only [h2446, h2451, h2455, h2520, hlam, ht23, ht34, ht45, u5elo1]
                                                          · linarith only [h2446, h2455, h2520, hlam, ht23, ht34, ht45, u5elo1]
                                                          · linarith only [h2446, h2520, hlam, ht23, ht34, ht45, u5elo1]
                                                  · linarith only [h2446, h2513, hlam]
                                                · linarith only [h2512, hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h0, h2269, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2458_1, p2489_1]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h0, h1953, h2446, h2451, h2455, hlam, p2458_1, p2489_2]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h0, h1953, h2446, h2455, hlam, p2458_1, p2489_2]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h0, h1953, h2446, hlam, p2458_1, p2489_2]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h1954, hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h2444, hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h2451, hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h2453, hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h1955, hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h2445, hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h0, h1953, h2446, h2455, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2458_1, p2489_1, u0elo1]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h2455, hlam, p2489_1]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h1956, hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h2446, hlam, p2489_0]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h0, h1953, h2446, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2458_1, p2489_1, u0elo1]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [h0, h1953, h2446, hc24, hlam, hphi, ht0b, ht45, ht5b, p2458_1, p2489_1, u0elo1]
                                              · have p2489_0 := h2489c.1
                                                have p2489_1 := h2489c.2.1
                                                have p2489_2 := h2489c.2.2.1
                                                have p2489_3 := h2489c.2.2.2
                                                linarith only [hlam, p2489_0]
                                      · linarith only [h1956, h2482, hlam]
                                    · linarith only [h1953, h2481, hlam]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h1951, h2444, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2458_1, u0elo1]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [hlam, p2458_0]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    rcases p2458_3 (m.d 0 1) (by simp) with h2630 | h2630
                                    · linarith only [h0, h2630, hlam]
                                    · linarith only [h1951, h2630, hlam]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    rcases p2458_3 (m.d 0 1) (by simp) with h2633 | h2633
                                    · linarith only [h0, h2633, hlam]
                                    · linarith only [h1952, h2633, hlam]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    rcases p2458_3 (m.d 0 1) (by simp) with h2636 | h2636
                                    · linarith only [h0, h2636, hlam]
                                    · linarith only [h1953, h2636, hlam]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h1951, hlam, p2458_1]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h1954, hlam, p2458_1]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [hlam, p2458_0]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h1957, hlam, p2458_1]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h2163, hlam, p2458_1]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h1952, hlam, p2458_0]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h1955, hlam, p2458_0]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h1951, h2269, h2444, hc23, hc45, hlam, hphi, ht34, p2458_1]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [hlam, p2458_0]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h2269, hlam, p2458_0]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h1953, hlam, p2458_0]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h1956, hlam, p2458_1]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h1951, h2163, h2444, hc23, hlam, hphi, ht34, ht45, p2458_1, u5elo3]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [h2163, hc04, hlam, hphi, ht45, p2458_1, u5elo3]
                                  · have p2458_0 := h2458c.1
                                    have p2458_1 := h2458c.2.1
                                    have p2458_2 := h2458c.2.2.1
                                    have p2458_3 := h2458c.2.2.2
                                    linarith only [hlam, p2458_0]
                                · linarith only [h1951, h1957, h2444, h2457, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h2446, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1951, h1955, h2444, h2445, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h1951, h1954, h2444, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
        · linarith only [h0, h1951, h1956, hc13, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h0, h1952, h1955, hlam]
    · linarith only [h0, h1951, h1954, hlam]
  · linarith only [h1951, h1953, hc13, hlam, hphi, ht34, ht45, u5elo1]

end R2N4
