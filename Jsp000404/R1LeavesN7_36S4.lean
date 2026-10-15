import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1494 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2055 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5ehi := hb5.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2056 | h2056
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2057 | h2057
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2058 | h2058
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2059 | h2059
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2060 | h2060
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2061 | h2061
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2062 | h2062
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2063 | h2063
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2064 | h2064
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2065 | h2065
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2066 | h2066
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2067 | h2067
                        · linarith only [h2055, h2067, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · linarith only [h2059, h2066, h2067, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2070 | h2070
                        · linarith only [h2055, h2058, h2066, h2070, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2072 | h2072
                          · linarith only [h2056, h2072, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2074 | h2074
                            · linarith only [h2055, h2058, h2066, h2072, h2074, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h2060, h2066, h2074, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1494, h2059, h2065, hlam]
                  · linarith only [h1494, h2058, h2064, hlam]
                · linarith only [h0, h2057, h2063, hlam]
              · linarith only [h0, h2056, h2062, hlam]
            · linarith only [h0, h2055, h2061, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2082 | h2082
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2083 | h2083
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2084 | h2084
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2085 | h2085
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2086 | h2086
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2087 | h2087
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2088 | h2088
                        · linarith only [h2055, h2088, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · linarith only [h2055, h2059, h2087, h2088, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2091 | h2091
                        · linarith only [h2055, h2091, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2093 | h2093
                          · linarith only [h2055, h2058, h2060, h2087, h2093, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2095 | h2095
                            · linarith only [h2058, h2060, h2095, hlam]
                            · rcases h2bigk with h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c | h2097c
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h0, hlam, p2097_1]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                rcases p2097_3 (m.d 0 2) (by simp) with h2100 | h2100
                                · rcases p2097_3 (m.d 1 2) (by simp) with h2101 | h2101
                                  · rcases p2097_3 (m.d 2 3) (by simp) with h2102 | h2102
                                    · linarith only [h2102, hlam, p2097_0]
                                    · rcases p2097_3 (m.d 2 4) (by simp) with h2104 | h2104
                                      · linarith only [h2056, h2104, hlam]
                                      · linarith only [h2087, h2104, hlam]
                                  · linarith only [h2082, h2101, hlam]
                                · linarith only [h2100, hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                rcases p2097_3 (m.d 0 2) (by simp) with h2109 | h2109
                                · rcases p2097_3 (m.d 1 2) (by simp) with h2110 | h2110
                                  · rcases p2097_3 (m.d 2 3) (by simp) with h2111 | h2111
                                    · linarith only [h2055, h2111, hlam]
                                    · rcases p2097_3 (m.d 2 4) (by simp) with h2113 | h2113
                                      · linarith only [h2113, hlam, p2097_0]
                                      · rcases p2097_3 (m.d 2 5) (by simp) with h2115 | h2115
                                        · linarith only [h2057, h2115, hlam]
                                        · linarith only [h2093, h2115, hlam]
                                  · linarith only [h2083, h2110, hlam]
                                · linarith only [h2109, hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p2097_1, u0elo1, u5ehi2]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2055, h2059, h2087, h2095, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2097_1]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                rcases p2097_3 (m.d 0 2) (by simp) with h2123 | h2123
                                · linarith only [h0, h2123, hlam]
                                · linarith only [h2055, h2123, hlam]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                rcases p2097_3 (m.d 0 2) (by simp) with h2126 | h2126
                                · linarith only [h0, h2126, hlam]
                                · linarith only [h2056, h2126, hlam]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                rcases p2097_3 (m.d 0 2) (by simp) with h2129 | h2129
                                · linarith only [h0, h2129, hlam]
                                · linarith only [h2057, h2129, hlam]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2055, hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2082, hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2087, hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2091, hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2056, hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2083, hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2056, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2097_1, u0elo1]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2093, hlam, p2097_1]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2057, hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2084, hlam, p2097_0]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2097_1, u0elo1]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [h2059, h2091, hc24, hlam, hphi, ht0b, ht45, ht5b, p2097_1, u0elo2]
                              · have p2097_0 := h2097c.1
                                have p2097_1 := h2097c.2.1
                                have p2097_2 := h2097c.2.2.1
                                have p2097_3 := h2097c.2.2.2
                                linarith only [hlam, p2097_0]
                    · linarith only [h1494, h2059, h2086, hlam]
                  · linarith only [h1494, h2058, h2059, h2085, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                · linarith only [h0, h2057, h2084, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h2056, h2083, hlam]
            · linarith only [h0, h2055, h2082, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2152 | h2152
          · linarith only [h2058, h2059, h2152, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2154 | h2154
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2155 | h2155
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2156 | h2156
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2157 | h2157
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2158 | h2158
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2159 | h2159
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2160 | h2160
                        · linarith only [h2055, h2059, h2160, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2162 | h2162
                          · linarith only [h2055, h2152, h2159, h2162, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2164 | h2164
                            · linarith only [h2056, h2152, h2159, h2164, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                            · rcases h2bigk with h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h0, hlam, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2159, hc34, hlam, hphi, ht0b, ht45, ht5b, p2166_1, u0elo1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                rcases p2166_3 (m.d 0 2) (by simp) with h2170 | h2170
                                · rcases p2166_3 (m.d 1 2) (by simp) with h2171 | h2171
                                  · rcases p2166_3 (m.d 2 3) (by simp) with h2172 | h2172
                                    · linarith only [h2055, h2172, hlam]
                                    · linarith only [h2159, h2172, hlam]
                                  · linarith only [h2155, h2171, hlam]
                                · linarith only [h2170, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2159, h2160, hc34, hlam, hphi, ht0b, ht45, ht5b, p2166_1, u0elo1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2055, h2159, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                rcases p2166_3 (m.d 0 2) (by simp) with h2180 | h2180
                                · linarith only [h0, h2180, hlam]
                                · linarith only [h2055, h2180, hlam]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                rcases p2166_3 (m.d 0 2) (by simp) with h2183 | h2183
                                · linarith only [h0, h2183, hlam]
                                · linarith only [h2056, h2183, hlam]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                rcases p2166_3 (m.d 0 2) (by simp) with h2186 | h2186
                                · linarith only [h0, h2186, hlam]
                                · linarith only [h2057, h2186, hlam]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2055, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2154, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2057, h2160, hc24, hlam, hphi, ht0b, ht45, ht5b, p2166_1, u0elo1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2160, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2056, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2155, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2159, hlam, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2162, hlam, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2057, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2156, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2166_1, u0elo1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2057, h2159, hc34, hlam, hphi, ht0b, ht45, ht5b, p2166_1, u0elo1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [hlam, p2166_0]
                      · linarith only [h2058, h2059, h2154, h2158, h2159, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2205 | h2205
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2206 | h2206
                        · linarith only [h1494, h2055, h2158, h2206, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2208 | h2208
                          · linarith only [h2056, h2152, h2208, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2210 | h2210
                            · linarith only [h2056, h2152, h2205, h2210, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                            · rcases h2bigk with h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c | h2212c
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h0, hlam, p2212_1]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2205, hc34, hlam, hphi, ht0b, ht45, ht5b, p2212_1, u0elo1]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                rcases p2212_3 (m.d 0 2) (by simp) with h2216 | h2216
                                · rcases p2212_3 (m.d 1 2) (by simp) with h2217 | h2217
                                  · rcases p2212_3 (m.d 2 3) (by simp) with h2218 | h2218
                                    · linarith only [h2055, h2218, hlam]
                                    · linarith only [h2205, h2218, hlam]
                                  · linarith only [h2155, h2217, hlam]
                                · linarith only [h2216, hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p2212_1, u0elo1, u5ehi2]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2055, h2205, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2212_1]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                rcases p2212_3 (m.d 0 2) (by simp) with h2226 | h2226
                                · linarith only [h0, h2226, hlam]
                                · linarith only [h2055, h2226, hlam]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                rcases p2212_3 (m.d 0 2) (by simp) with h2229 | h2229
                                · linarith only [h0, h2229, hlam]
                                · linarith only [h2056, h2229, hlam]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                rcases p2212_3 (m.d 0 2) (by simp) with h2232 | h2232
                                · linarith only [h0, h2232, hlam]
                                · linarith only [h2057, h2232, hlam]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2055, hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2154, hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2057, h2205, h2206, hc34, hlam, hphi, ht0b, ht45, ht5b, p2212_1, u0elo1]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2206, hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2056, hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2155, hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2205, hlam, p2212_1]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2208, hlam, p2212_1]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2057, hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2156, hlam, p2212_0]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2212_1, u0elo1]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [h2057, h2205, hc34, hlam, hphi, ht0b, ht45, ht5b, p2212_1, u0elo1]
                              · have p2212_0 := h2212c.1
                                have p2212_1 := h2212c.2.1
                                have p2212_2 := h2212c.2.2.1
                                have p2212_3 := h2212c.2.2.2
                                linarith only [hlam, p2212_0]
                      · linarith only [h1494, h2058, h2158, h2205, hc23, hc35, hlam, hphi]
                  · linarith only [h1494, h2058, h2157, hlam]
                · linarith only [h0, h2057, h2156, hlam]
              · linarith only [h0, h2056, h2155, hlam]
            · linarith only [h0, h2055, h2154, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2255 | h2255
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2256 | h2256
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2257 | h2257
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2258 | h2258
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2259 | h2259
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2260 | h2260
                  · linarith only [h2058, h2255, h2260, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2262 | h2262
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2263 | h2263
                      · linarith only [h2055, h2260, h2263, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2265 | h2265
                        · linarith only [h2056, h2263, h2265, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · linarith only [h1494, h2255, h2260, h2265, hc23, hc34, hlam, hphi]
                    · linarith only [h1494, h2255, h2262, hlam]
                · linarith only [h0, h2057, h2259, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h2056, h2258, hlam]
            · linarith only [h0, h2055, h2257, hlam]
          · linarith only [h2058, h2255, h2256, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2273 | h2273
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2274 | h2274
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2275 | h2275
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2276 | h2276
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2277 | h2277
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2278 | h2278
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2279 | h2279
                      · linarith only [h2055, h2058, h2273, h2279, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2281 | h2281
                        · linarith only [h2055, h2255, h2281, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2283 | h2283
                          · linarith only [h2056, h2283, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2285 | h2285
                            · rcases h2bigk with h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c | h2286c
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h0, hlam, p2286_1]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                rcases p2286_3 (m.d 0 2) (by simp) with h2289 | h2289
                                · rcases p2286_3 (m.d 1 2) (by simp) with h2290 | h2290
                                  · rcases p2286_3 (m.d 2 3) (by simp) with h2291 | h2291
                                    · linarith only [h2291, hlam, p2286_0]
                                    · rcases p2286_3 (m.d 2 4) (by simp) with h2293 | h2293
                                      · linarith only [h2056, h2293, hlam]
                                      · linarith only [h2279, h2293, hlam]
                                  · linarith only [h2274, h2290, hlam]
                                · linarith only [h2289, hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                rcases p2286_3 (m.d 0 2) (by simp) with h2298 | h2298
                                · rcases p2286_3 (m.d 1 2) (by simp) with h2299 | h2299
                                  · rcases p2286_3 (m.d 2 3) (by simp) with h2300 | h2300
                                    · linarith only [h2055, h2300, hlam]
                                    · rcases p2286_3 (m.d 2 4) (by simp) with h2302 | h2302
                                      · linarith only [h2302, hlam, p2286_0]
                                      · rcases p2286_3 (m.d 2 5) (by simp) with h2304 | h2304
                                        · linarith only [h2057, h2304, hlam]
                                        · linarith only [h2283, h2304, hlam]
                                  · linarith only [h2275, h2299, hlam]
                                · linarith only [h2298, hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p2286_1, u0elo1, u5ehi2]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2056, h2273, h2279, h2283, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2286_1]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2058, h2273, h2274, h2277, h2279, h2283, hlam, p2286_2]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2058, h2273, h2274, h2277, h2283, hlam, p2286_2]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                rcases p2286_3 (m.d 0 2) (by simp) with h2314 | h2314
                                · linarith only [h0, h2314, hlam]
                                · linarith only [h2057, h2314, hlam]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2055, hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2274, hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2279, hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2281, hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2056, hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2275, hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2056, h2273, h2283, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2286_1, u0elo1]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2283, hlam, p2286_1]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2057, hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2276, hlam, p2286_0]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2286_1, u0elo1]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [h2058, h2273, h2274, h2277, h2283, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2286_1]
                              · have p2286_0 := h2286c.1
                                have p2286_1 := h2286c.2.1
                                have p2286_2 := h2286c.2.2.1
                                have p2286_3 := h2286c.2.2.2
                                linarith only [hlam, p2286_0]
                            · linarith only [h2058, h2273, h2285, hlam]
                    · linarith only [h2058, h2273, h2277, h2278, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2334 | h2334
                    · linarith only [h1494, h2255, h2277, h2334, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2336 | h2336
                      · linarith only [h1494, h2277, h2336, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2338 | h2338
                        · linarith only [h1494, h2055, h2334, h2338, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2340 | h2340
                          · linarith only [h2056, h2340, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2342 | h2342
                            · rcases h2bigk with h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h0, hlam, p2343_1]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                rcases p2343_3 (m.d 0 2) (by simp) with h2346 | h2346
                                · rcases p2343_3 (m.d 1 2) (by simp) with h2347 | h2347
                                  · rcases p2343_3 (m.d 2 3) (by simp) with h2348 | h2348
                                    · linarith only [h2348, hlam, p2343_0]
                                    · rcases p2343_3 (m.d 2 4) (by simp) with h2350 | h2350
                                      · linarith only [h2056, h2350, hlam]
                                      · linarith only [h2336, h2350, hlam]
                                  · linarith only [h2274, h2347, hlam]
                                · linarith only [h2346, hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                rcases p2343_3 (m.d 0 2) (by simp) with h2355 | h2355
                                · rcases p2343_3 (m.d 1 2) (by simp) with h2356 | h2356
                                  · rcases p2343_3 (m.d 2 3) (by simp) with h2357 | h2357
                                    · linarith only [h2055, h2357, hlam]
                                    · rcases p2343_3 (m.d 2 4) (by simp) with h2359 | h2359
                                      · linarith only [h2359, hlam, p2343_0]
                                      · rcases p2343_3 (m.d 2 5) (by simp) with h2361 | h2361
                                        · linarith only [h2057, h2361, hlam]
                                        · linarith only [h2340, h2361, hlam]
                                  · linarith only [h2275, h2356, hlam]
                                · linarith only [h2355, hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p2343_1, u0elo1, u5ehi2]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2056, h2273, h2336, h2340, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2343_1]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                rcases p2343_3 (m.d 0 2) (by simp) with h2369 | h2369
                                · linarith only [h0, h2369, hlam]
                                · linarith only [h2055, h2369, hlam]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                rcases p2343_3 (m.d 0 2) (by simp) with h2372 | h2372
                                · linarith only [h0, h2372, hlam]
                                · linarith only [h2056, h2372, hlam]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                rcases p2343_3 (m.d 0 2) (by simp) with h2375 | h2375
                                · linarith only [h0, h2375, hlam]
                                · linarith only [h2057, h2375, hlam]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2055, hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2274, hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2336, hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2338, hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2056, hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2275, hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2056, h2273, h2340, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2343_1, u0elo1]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2340, hlam, p2343_1]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2057, hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2276, hlam, p2343_0]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2343_1, u0elo1]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [h2056, h2273, h2340, hc24, hlam, hphi, ht0b, ht45, ht5b, p2343_1, u0elo1]
                              · have p2343_0 := h2343c.1
                                have p2343_1 := h2343c.2.1
                                have p2343_2 := h2343c.2.2.1
                                have p2343_3 := h2343c.2.2.2
                                linarith only [hlam, p2343_0]
                            · linarith only [h2056, h2058, h2273, h2342, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h2057, h2276, hlam]
              · linarith only [h0, h2056, h2275, hlam]
            · linarith only [h0, h2055, h2274, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2397 | h2397
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2398 | h2398
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2399 | h2399
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2400 | h2400
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2401 | h2401
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2402 | h2402
                      · linarith only [h2055, h2058, h2402, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2404 | h2404
                        · linarith only [h2055, h2255, h2404, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2406 | h2406
                          · linarith only [h2056, h2058, h2273, h2406, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2408 | h2408
                            · linarith only [h1494, h2058, h2273, h2400, h2408, hc01, hc13, hlam, hphi]
                            · rcases h2bigk with h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h0, hlam, p2410_1]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                rcases p2410_3 (m.d 0 2) (by simp) with h2413 | h2413
                                · rcases p2410_3 (m.d 1 2) (by simp) with h2414 | h2414
                                  · rcases p2410_3 (m.d 2 3) (by simp) with h2415 | h2415
                                    · linarith only [h2415, hlam, p2410_0]
                                    · rcases p2410_3 (m.d 2 4) (by simp) with h2417 | h2417
                                      · linarith only [h2056, h2417, hlam]
                                      · linarith only [h2402, h2417, hlam]
                                  · linarith only [h2397, h2414, hlam]
                                · linarith only [h2413, hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                rcases p2410_3 (m.d 0 2) (by simp) with h2422 | h2422
                                · rcases p2410_3 (m.d 1 2) (by simp) with h2423 | h2423
                                  · rcases p2410_3 (m.d 2 3) (by simp) with h2424 | h2424
                                    · linarith only [h2055, h2424, hlam]
                                    · rcases p2410_3 (m.d 2 4) (by simp) with h2426 | h2426
                                      · linarith only [h2426, hlam, p2410_0]
                                      · rcases p2410_3 (m.d 2 5) (by simp) with h2428 | h2428
                                        · linarith only [h2057, h2428, hlam]
                                        · linarith only [h2406, h2428, hlam]
                                  · linarith only [h2398, h2423, hlam]
                                · linarith only [h2422, hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p2410_1, u0elo1, u5ehi2]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2057, hc12, hlam, hphi, ht01, ht0b, ht5b, p2410_1, u5ehi2]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                rcases p2410_3 (m.d 0 2) (by simp) with h2436 | h2436
                                · linarith only [h0, h2436, hlam]
                                · linarith only [h2055, h2436, hlam]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                rcases p2410_3 (m.d 0 2) (by simp) with h2439 | h2439
                                · linarith only [h0, h2439, hlam]
                                · linarith only [h2056, h2439, hlam]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                rcases p2410_3 (m.d 0 2) (by simp) with h2442 | h2442
                                · linarith only [h0, h2442, hlam]
                                · linarith only [h2057, h2442, hlam]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2055, hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2397, hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2402, hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2404, hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2056, hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2398, hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2057, h2406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2410_1, u0elo1]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2406, hlam, p2410_1]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2057, hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2399, hlam, p2410_0]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2410_1, u0elo1]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [h2057, hc24, hlam, hphi, ht0b, ht45, ht5b, p2410_1, u0elo1]
                              · have p2410_0 := h2410c.1
                                have p2410_1 := h2410c.2.1
                                have p2410_2 := h2410c.2.2.1
                                have p2410_3 := h2410c.2.2.2
                                linarith only [hlam, p2410_0]
                    · linarith only [h1494, h2058, h2400, h2401, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2461 | h2461
                    · linarith only [h1494, h2255, h2400, h2461, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2463 | h2463
                      · linarith only [h1494, h2400, h2463, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2465 | h2465
                        · linarith only [h1494, h2461, h2465, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2467 | h2467
                          · linarith only [h2056, h2467, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2469 | h2469
                            · rcases h2bigk with h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h0, hlam, p2470_1]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                rcases p2470_3 (m.d 0 2) (by simp) with h2473 | h2473
                                · rcases p2470_3 (m.d 1 2) (by simp) with h2474 | h2474
                                  · rcases p2470_3 (m.d 2 3) (by simp) with h2475 | h2475
                                    · linarith only [h2475, hlam, p2470_0]
                                    · rcases p2470_3 (m.d 2 4) (by simp) with h2477 | h2477
                                      · linarith only [h2056, h2477, hlam]
                                      · linarith only [h2463, h2477, hlam]
                                  · linarith only [h2397, h2474, hlam]
                                · linarith only [h2473, hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                rcases p2470_3 (m.d 0 2) (by simp) with h2482 | h2482
                                · rcases p2470_3 (m.d 1 2) (by simp) with h2483 | h2483
                                  · rcases p2470_3 (m.d 2 3) (by simp) with h2484 | h2484
                                    · linarith only [h2055, h2484, hlam]
                                    · rcases p2470_3 (m.d 2 4) (by simp) with h2486 | h2486
                                      · linarith only [h2486, hlam, p2470_0]
                                      · rcases p2470_3 (m.d 2 5) (by simp) with h2488 | h2488
                                        · linarith only [h2057, h2488, hlam]
                                        · linarith only [h2467, h2488, hlam]
                                  · linarith only [h2398, h2483, hlam]
                                · linarith only [h2482, hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p2470_1, u0elo1, u5ehi2]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2057, hc12, hlam, hphi, ht01, ht0b, ht5b, p2470_1, u5ehi2]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                rcases p2470_3 (m.d 0 2) (by simp) with h2496 | h2496
                                · linarith only [h0, h2496, hlam]
                                · linarith only [h2055, h2496, hlam]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                rcases p2470_3 (m.d 0 2) (by simp) with h2499 | h2499
                                · linarith only [h0, h2499, hlam]
                                · linarith only [h2056, h2499, hlam]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                rcases p2470_3 (m.d 0 2) (by simp) with h2502 | h2502
                                · linarith only [h0, h2502, hlam]
                                · linarith only [h2057, h2502, hlam]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2055, hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2397, hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2463, hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2465, hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2056, hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2398, hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2056, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2470_1, u0elo1]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2467, hlam, p2470_1]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2057, hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2399, hlam, p2470_0]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2470_1, u0elo1]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [h2057, hc24, hlam, hphi, ht0b, ht45, ht5b, p2470_1, u0elo1]
                              · have p2470_0 := h2470c.1
                                have p2470_1 := h2470c.2.1
                                have p2470_2 := h2470c.2.2.1
                                have p2470_3 := h2470c.2.2.2
                                linarith only [hlam, p2470_0]
                            · linarith only [h1494, h2400, h2469, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h2057, h2399, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h2056, h2398, hlam]
            · linarith only [h0, h2055, h2397, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2524 | h2524
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2525 | h2525
        · linarith only [h2055, h2057, h2525, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2527 | h2527
          · linarith only [h2056, h2057, h2527, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2529 | h2529
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2530 | h2530
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2531 | h2531
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2532 | h2532
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2533 | h2533
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2534 | h2534
                      · linarith only [h2055, h2057, h2531, h2534, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h2055, h2057, h2524, h2531, h2534, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2537 | h2537
                      · linarith only [h2055, h2057, h2531, h2537, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h2055, h2057, h2524, h2531, h2537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h2055, h2057, h2524, h2531, h2532, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2541 | h2541
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2542 | h2542
                    · linarith only [h2524, h2525, h2529, h2531, h2542, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2544 | h2544
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2545 | h2545
                        · linarith only [h2055, h2542, h2545, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2547 | h2547
                          · linarith only [h0, h2056, h2527, h2531, h2545, h2547, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                          · linarith only [h0, h2055, h2531, h2544, h2547, hc34, hc45, hlam, hphi]
                      · linarith only [h2524, h2525, h2544, hc23, hc35, hlam, hphi]
                  · linarith only [h1494, h2524, h2541, hlam]
              · linarith only [h0, h2056, h2530, hlam]
            · linarith only [h0, h2055, h2529, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2554 | h2554
        · linarith only [h2056, h2057, h2524, h2554, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2556 | h2556
          · linarith only [h2056, h2057, h2556, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2558 | h2558
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2559 | h2559
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2560 | h2560
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2561 | h2561
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2562 | h2562
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2563 | h2563
                      · linarith only [h2055, h2524, h2563, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2565 | h2565
                        · linarith only [h2056, h2057, h2554, h2560, h2563, h2565, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2567 | h2567
                          · linarith only [h2056, h2057, h2558, h2562, h2565, h2567, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2569 | h2569
                            · linarith only [h2056, h2057, h2563, h2567, h2569, hc23, hc34, hlam, hphi]
                            · rcases h2bigk with h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h0, hlam, p2571_1]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2057, h2558, h2562, h2565, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2571_1]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2057, h2558, h2562, h2565, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2571_1]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2057, hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                rcases p2571_3 (m.d 0 2) (by simp) with h2577 | h2577
                                · linarith only [h0, h2577, hlam]
                                · rcases p2571_3 (m.d 1 2) (by simp) with h2579 | h2579
                                  · rcases p2571_3 (m.d 2 3) (by simp) with h2580 | h2580
                                    · linarith only [h2558, h2580, hlam]
                                    · rcases p2571_3 (m.d 2 4) (by simp) with h2582 | h2582
                                      · linarith only [h2559, h2582, hlam]
                                      · rcases p2571_3 (m.d 2 5) (by simp) with h2584 | h2584
                                        · linarith only [h2560, h2584, hlam]
                                        · linarith only [h2057, h2584, hlam]
                                  · linarith only [h0, h2579, hlam]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2055, h2057, h2558, h2562, h2565, hlam, p2571_2]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2056, h2057, h2558, h2562, h2565, hlam, p2571_2]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2056, h2057, h2563, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2571_1]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2055, hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2558, hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2563, hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2565, hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2056, hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2559, hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2056, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2571_1, u0elo1]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2567, hlam, p2571_1]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2056, h2560, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2571_1]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [h2560, hlam, p2571_0]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                rcases p2571_3 (m.d 0 2) (by simp) with h2604 | h2604
                                · linarith only [h2057, h2604, hlam]
                                · linarith only [h2055, h2604, hlam]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                rcases p2571_3 (m.d 0 2) (by simp) with h2607 | h2607
                                · linarith only [h2057, h2607, hlam]
                                · linarith only [h2056, h2607, hlam]
                              · have p2571_0 := h2571c.1
                                have p2571_1 := h2571c.2.1
                                have p2571_2 := h2571c.2.2.1
                                have p2571_3 := h2571c.2.2.2
                                linarith only [hlam, p2571_0]
                    · linarith only [h1494, h2524, h2561, h2562, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2612 | h2612
                    · linarith only [h1494, h2554, h2561, h2612, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2614 | h2614
                      · linarith only [h2055, h2561, h2614, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2616 | h2616
                        · linarith only [h2056, h2612, h2614, h2616, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2618 | h2618
                          · linarith only [h2056, h2057, h2560, h2618, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2620 | h2620
                            · linarith only [h2056, h2057, h2614, h2618, h2620, hc23, hc34, hlam, hphi]
                            · linarith only [h1494, h2561, h2620, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2623 | h2623
                  · linarith only [h1494, h2524, h2558, h2560, h2623, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2625 | h2625
                    · linarith only [h2554, h2623, h2625, hc03, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2627 | h2627
                      · linarith only [h1494, h2055, h2623, h2627, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2629 | h2629
                        · linarith only [h0, h1494, h2056, h2560, h2625, h2627, h2629, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2631 | h2631
                          · linarith only [h0, h2056, h2560, h2629, h2631, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2633 | h2633
                            · linarith only [h0, h2056, h2560, h2627, h2631, h2633, hc23, hc34, hlam, hphi]
                            · linarith only [h1494, h2623, h2633, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h2056, h2559, hlam]
            · linarith only [h0, h2055, h2558, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2638 | h2638
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2639 | h2639
      · linarith only [h2055, h2056, h2639, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2641 | h2641
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2642 | h2642
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2643 | h2643
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2644 | h2644
              · linarith only [h2056, h2638, h2644, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2646 | h2646
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2647 | h2647
                  · linarith only [h2639, h2641, h2647, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2649 | h2649
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2650 | h2650
                      · linarith only [h2055, h2647, h2650, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2652 | h2652
                        · linarith only [h0, h2055, h2644, h2650, h2652, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h0, h2055, h2641, h2644, h2650, h2652, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1494, h2638, h2641, h2644, h2649, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2638, h2646, hlam]
            · linarith only [h0, h2055, h2643, hlam]
          · linarith only [h2055, h2056, h2641, h2642, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2659 | h2659
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2660 | h2660
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2661 | h2661
              · linarith only [h2056, h2638, h2661, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2663 | h2663
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2664 | h2664
                  · linarith only [h1494, h2639, h2660, h2661, h2664, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2666 | h2666
                    · linarith only [h1494, h2641, h2660, h2661, h2666, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2668 | h2668
                      · linarith only [h1494, h2055, h2664, h2668, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2670 | h2670
                        · linarith only [h0, h1494, h2055, h2661, h2666, h2668, h2670, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2672 | h2672
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2673 | h2673
                            · rcases h2bigk with h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h0, hlam, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h0, h2661, h2668, hc23, hc34, hlam, hphi, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2056, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h0, h2661, h2668, h2672, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2674_1, u5ehi4]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2661, h2668, hc02, hc34, hlam, hphi, ht23, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2661, h2668, hc23, hc34, hlam, hphi, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2661, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2661, h2668, h2672, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2674_1, u5ehi4]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2055, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2660, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2668, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2670, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2638, h2668, h2672, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2674_1, u5ehi4]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h0, h2668, hc01, hc34, hlam, hphi, ht12, ht23, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                rcases p2674_3 (m.d 0 2) (by simp) with h2692 | h2692
                                · linarith only [h2056, h2692, hlam]
                                · linarith only [h2055, h2692, hlam]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                rcases p2674_3 (m.d 0 2) (by simp) with h2696 | h2696
                                · linarith only [h2056, h2696, hlam]
                                · linarith only [h2638, h2696, hlam]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2638, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2663, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2638, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2674_1, u0elo1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2672, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [hlam, p2674_0]
                            · linarith only [h0, h2638, h2661, h2668, h2672, h2673, hlam]
                          · linarith only [h0, h2638, h2661, h2672, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                · linarith only [h0, h2638, h2663, hlam]
            · linarith only [h0, h2055, h2660, hlam]
          · linarith only [h2056, h2638, h2659, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2709 | h2709
      · linarith only [h2055, h2056, h2709, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2711 | h2711
        · linarith only [h2055, h2638, h2711, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2713 | h2713
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2714 | h2714
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2715 | h2715
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2716 | h2716
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2717 | h2717
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2718 | h2718
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2719 | h2719
                      · linarith only [h2055, h2056, h2709, h2715, h2719, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2721 | h2721
                        · linarith only [h1494, h2055, h2056, h2711, h2714, h2717, h2719, h2721, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2723 | h2723
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2724 | h2724
                            · rcases h2bigk with h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h0, hlam, p2725_1]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2638, h2714, h2717, h2719, h2723, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2725_1]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2056, hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2638, hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                rcases p2725_3 (m.d 0 2) (by simp) with h2731 | h2731
                                · linarith only [h0, h2731, hlam]
                                · rcases p2725_3 (m.d 1 2) (by simp) with h2733 | h2733
                                  · rcases p2725_3 (m.d 2 3) (by simp) with h2734 | h2734
                                    · linarith only [h2714, h2734, hlam]
                                    · rcases p2725_3 (m.d 2 4) (by simp) with h2736 | h2736
                                      · linarith only [h2715, h2736, hlam]
                                      · linarith only [h2056, h2736, hlam]
                                  · linarith only [h0, h2733, hlam]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2055, h2638, h2714, h2717, h2719, h2723, hlam, p2725_2]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2055, h2638, h2723, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2725_1]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2055, h2638, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2725_1]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2055, hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2714, hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2719, hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2721, hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2055, h2715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2725_1]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2715, hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                rcases p2725_3 (m.d 0 2) (by simp) with h2751 | h2751
                                · linarith only [h2056, h2751, hlam]
                                · linarith only [h2055, h2751, hlam]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2055, h2638, h2714, h2717, h2719, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2725_1]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2055, h2721, hc23, hc35, hlam, hphi, p2725_1]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2716, hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                rcases p2725_3 (m.d 0 2) (by simp) with h2758 | h2758
                                · linarith only [h2638, h2758, hlam]
                                · linarith only [h2055, h2758, hlam]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [h2723, hlam, p2725_0]
                              · have p2725_0 := h2725c.1
                                have p2725_1 := h2725c.2.1
                                have p2725_2 := h2725c.2.2.1
                                have p2725_3 := h2725c.2.2.2
                                linarith only [hlam, p2725_0]
                            · linarith only [h2713, h2719, h2723, h2724, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
                          · linarith only [h2056, h2713, h2723, hlam]
                    · linarith only [h1494, h2709, h2717, h2718, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2766 | h2766
                    · linarith only [h1494, h2711, h2717, h2766, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2768 | h2768
                      · linarith only [h2055, h2717, h2768, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2770 | h2770
                        · linarith only [h2055, h2056, h2715, h2766, h2770, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2772 | h2772
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2773 | h2773
                            · rcases h2bigk with h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c | h2774c
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h0, hlam, p2774_1]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2638, h2715, h2772, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2774_1]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2056, hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2638, hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                rcases p2774_3 (m.d 0 2) (by simp) with h2780 | h2780
                                · linarith only [h0, h2780, hlam]
                                · rcases p2774_3 (m.d 1 2) (by simp) with h2782 | h2782
                                  · rcases p2774_3 (m.d 2 3) (by simp) with h2783 | h2783
                                    · linarith only [h2714, h2783, hlam]
                                    · rcases p2774_3 (m.d 2 4) (by simp) with h2785 | h2785
                                      · linarith only [h2715, h2785, hlam]
                                      · linarith only [h2056, h2785, hlam]
                                  · linarith only [h0, h2782, hlam]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2055, h2638, h2715, h2772, hlam, p2774_2]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2056, h2713, hc12, hlam, hphi, ht01, ht0b, ht5b, p2774_1, u5ehi4]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2055, h2638, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2774_1]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2055, hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2714, hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2768, hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2770, hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2055, h2715, h2717, hc23, hc34, hlam, hphi, p2774_1]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2715, hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                rcases p2774_3 (m.d 0 2) (by simp) with h2800 | h2800
                                · linarith only [h2056, h2800, hlam]
                                · linarith only [h2055, h2800, hlam]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2055, h2638, h2715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2774_1]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2055, h2716, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2774_1]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2716, hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                rcases p2774_3 (m.d 0 2) (by simp) with h2807 | h2807
                                · linarith only [h2638, h2807, hlam]
                                · linarith only [h2055, h2807, hlam]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [h2772, hlam, p2774_0]
                              · have p2774_0 := h2774c.1
                                have p2774_1 := h2774c.2.1
                                have p2774_2 := h2774c.2.2.1
                                have p2774_3 := h2774c.2.2.2
                                linarith only [hlam, p2774_0]
                            · linarith only [h1494, h2056, h2709, h2713, h2715, h2773, hc01, hc12, hlam, hphi]
                          · linarith only [h2056, h2713, h2772, hlam]
                · linarith only [h2056, h2713, h2715, h2716, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2815 | h2815
                · linarith only [h2055, h2638, h2715, h2815, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2817 | h2817
                  · linarith only [h2709, h2713, h2714, h2715, h2817, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2819 | h2819
                    · linarith only [h1494, h2711, h2817, h2819, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2821 | h2821
                      · linarith only [h2055, h2817, h2821, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2823 | h2823
                        · linarith only [h0, h2055, h2711, h2715, h2821, h2823, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2825 | h2825
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2826 | h2826
                            · rcases h2bigk with h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c | h2827c
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h0, hlam, p2827_1]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h0, h2815, h2821, h2825, hc23, hc34, hlam, hphi, p2827_1]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2056, hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2638, hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2815, h2821, h2825, hc02, hc34, hlam, hphi, ht23, p2827_1]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2815, h2821, h2825, hc23, hc34, hlam, hphi, p2827_1]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2715, hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2815, hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2055, hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2714, hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2821, hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2823, hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2055, h2821, hc23, hc34, hlam, hphi, p2827_1]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h0, h2821, hc01, hc34, hlam, hphi, ht12, ht23, p2827_1]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                rcases p2827_3 (m.d 0 2) (by simp) with h2845 | h2845
                                · linarith only [h2056, h2845, hlam]
                                · linarith only [h2055, h2845, hlam]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2055, h2638, h2821, hc23, hc34, hlam, hphi, p2827_1]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2055, h2823, hc23, hc35, hlam, hphi, p2827_1]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h1494, h2714, h2823, hc01, hc35, hlam, hphi, ht12, ht23, p2827_1]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                rcases p2827_3 (m.d 0 2) (by simp) with h2852 | h2852
                                · linarith only [h2638, h2852, hlam]
                                · linarith only [h2055, h2852, hlam]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [h2825, hlam, p2827_0]
                              · have p2827_0 := h2827c.1
                                have p2827_1 := h2827c.2.1
                                have p2827_2 := h2827c.2.2.1
                                have p2827_3 := h2827c.2.2.2
                                linarith only [hlam, p2827_0]
                            · linarith only [h2055, h2056, h2821, h2826, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h1494, h2713, h2714, h2715, h2825, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
            · linarith only [h0, h2055, h2714, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2860 | h2860
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2861 | h2861
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2862 | h2862
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2863 | h2863
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2864 | h2864
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2865 | h2865
                      · linarith only [h1494, h2055, h2709, h2865, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2867 | h2867
                        · linarith only [h2055, h2056, h2711, h2860, h2863, h2865, h2867, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2869 | h2869
                          · linarith only [h2055, h2056, h2713, h2860, h2863, h2865, h2869, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h2055, h2056, h2869, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1494, h2709, h2863, h2864, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2873 | h2873
                    · linarith only [h1494, h2711, h2863, h2873, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2875 | h2875
                      · linarith only [h2055, h2863, h2875, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2877 | h2877
                        · linarith only [h1494, h2055, h2873, h2877, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2879 | h2879
                          · linarith only [h2055, h2056, h2713, h2861, h2863, h2879, hc23, hc34, hlam, hphi]
                          · linarith only [h2055, h2056, h2879, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h2055, h2056, h2861, h2862, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2883 | h2883
                · linarith only [h2055, h2638, h2861, h2883, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2885 | h2885
                  · linarith only [h1494, h2709, h2860, h2861, h2885, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2887 | h2887
                    · linarith only [h1494, h2711, h2885, h2887, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2889 | h2889
                      · linarith only [h2055, h2885, h2889, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2891 | h2891
                        · linarith only [h2055, h2056, h2711, h2713, h2891, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2893 | h2893
                          · linarith only [h2055, h2056, h2713, h2889, h2893, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h2861, h2893, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h2055, h2860, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]

end R2N4
