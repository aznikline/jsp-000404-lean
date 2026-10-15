import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5714000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h2026 | h2026
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2027 | h2027
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2028 | h2028
      · linarith only [h0, h1, h2028, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2030 | h2030
        · linarith only [h0, h1, h2026, h2030, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2032 | h2032
          · linarith only [h0, h1, h2027, h2032, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2034 | h2034
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2035 | h2035
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2036 | h2036
                · linarith only [h0, h2028, h2036, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2038 | h2038
                  · linarith only [h0, h1, h2032, h2035, h2038, hlam]
                  · linarith only [h0, h1, h2034, h2038, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h2027, h2034, h2035, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2026, h2028, h2034, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2043 | h2043
      · linarith only [h0, h1, h2043, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2045 | h2045
        · linarith only [h0, h1, h2026, h2045, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2047 | h2047
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2048 | h2048
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2049 | h2049
              · linarith only [h0, h1, h2027, h2047, h2049, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2051 | h2051
                · linarith only [h0, h1, h2043, h2051, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2053 | h2053
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2054 | h2054
                    · linarith only [h0, h1, h2048, h2049, h2053, h2054, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1, h2048, h2049, h2053, h2054, hc23, hc34, hlam, hphi]
                  · linarith only [h2047, h2048, h2049, h2053, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
            · linarith only [h2026, h2027, h2048, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2059 | h2059
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2060 | h2060
              · linarith only [h0, h1, h2027, h2060, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2062 | h2062
                · linarith only [h0, h2043, h2062, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2064 | h2064
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2065 | h2065
                    · linarith only [h0, h1, h2047, h2059, h2060, h2064, h2065, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1, h2047, h2059, h2060, h2064, h2065, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h2059, h2064, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h2026, h2027, h2059, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2070 | h2070
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2071 | h2071
      · linarith only [h0, h1, h2071, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2073 | h2073
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2074 | h2074
          · linarith only [h0, h1, h2070, h2074, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2076 | h2076
            · linarith only [h0, h2026, h2076, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2078 | h2078
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2079 | h2079
                · linarith only [h0, h1, h2071, h2079, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2081 | h2081
                  · linarith only [h0, h2074, h2078, h2081, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h2078, h2081, hc24, hc45, hlam, hphi]
              · linarith only [h2026, h2070, h2078, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2085 | h2085
          · linarith only [h0, h1, h2070, h2085, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2087 | h2087
            · linarith only [h0, h2026, h2087, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2089 | h2089
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2090 | h2090
                · linarith only [h0, h2071, h2090, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2092 | h2092
                  · linarith only [h0, h1, h2085, h2089, h2092, hlam]
                  · linarith only [h0, h1, h2089, h2092, hc24, hc45, hlam, hphi]
              · linarith only [h2026, h2070, h2089, hc12, hc23, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2096 | h2096
      · linarith only [h0, h1, h2096, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2098 | h2098
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2099 | h2099
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2100 | h2100
            · linarith only [h0, h2026, h2100, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2102 | h2102
              · linarith only [h0, h1, h2070, h2099, h2102, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2104 | h2104
                · linarith only [h0, h2096, h2104, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2106 | h2106
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2107 | h2107
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2108 | h2108
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2109 | h2109
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2110 | h2110
                          · rcases h2bigk with h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c | h2111c
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h0, h1, h2102, h2106, h2107, hc12, hc23, hlam, hphi, p2111_1]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h2026, hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h2070, hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h2096, hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h0, hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h2100, hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h2102, hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h2104, hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              rcases p2111_3 (m.d 0 2) (by simp) with h2122 | h2122
                              · linarith only [h2122, hlam, p2111_0]
                              · rcases p2111_3 (m.d 1 2) (by simp) with h2124 | h2124
                                · linarith only [h2100, h2124, hlam]
                                · rcases p2111_3 (m.d 2 3) (by simp) with h2126 | h2126
                                  · rcases p2111_3 (m.d 2 4) (by simp) with h2127 | h2127
                                    · linarith only [h2107, h2127, hlam]
                                    · linarith only [h2070, h2127, hlam]
                                  · linarith only [h2126, hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              rcases p2111_3 (m.d 0 2) (by simp) with h2131 | h2131
                              · linarith only [h2026, h2131, hlam]
                              · linarith only [h0, h2131, hlam]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h1, h2102, h2106, hc01, hc23, hlam, hphi, ht12, p2111_1]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h2096, hc02, hc23, hlam, hphi, p2111_1]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              rcases p2111_3 (m.d 0 2) (by simp) with h2137 | h2137
                              · linarith only [h2137, hlam, p2111_0]
                              · rcases p2111_3 (m.d 1 2) (by simp) with h2139 | h2139
                                · linarith only [h2102, h2139, hlam]
                                · rcases p2111_3 (m.d 2 3) (by simp) with h2141 | h2141
                                  · rcases p2111_3 (m.d 2 4) (by simp) with h2142 | h2142
                                    · rcases p2111_3 (m.d 2 5) (by simp) with h2143 | h2143
                                      · linarith only [h2109, h2143, hlam]
                                      · linarith only [h2096, h2143, hlam]
                                    · linarith only [h2142, hlam, p2111_0]
                                  · linarith only [h2026, h2141, hlam]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              rcases p2111_3 (m.d 0 2) (by simp) with h2148 | h2148
                              · linarith only [h2070, h2148, hlam]
                              · linarith only [h0, h2148, hlam]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h2107, hlam, p2111_1]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h0, h1, h2104, hc12, hc24, hlam, hphi, p2111_1]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              rcases p2111_3 (m.d 0 2) (by simp) with h2154 | h2154
                              · linarith only [h2154, hlam, p2111_0]
                              · rcases p2111_3 (m.d 1 2) (by simp) with h2156 | h2156
                                · linarith only [h2104, h2156, hlam]
                                · rcases p2111_3 (m.d 2 3) (by simp) with h2158 | h2158
                                  · rcases p2111_3 (m.d 2 4) (by simp) with h2159 | h2159
                                    · rcases p2111_3 (m.d 2 5) (by simp) with h2160 | h2160
                                      · rcases h5bigk with h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h1, hlam, p2161_1]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h2096, hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [hc35, hlam, hphi, ht0b, ht5b, p2161_1, u0elo4]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h2098, hc45, hlam, hphi, ht0b, ht5b, p2161_1, u0elo2]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h1, h2104, hc01, hc25, hlam, hphi, ht12, p2161_1]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h2104, hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          rcases p2161_3 (m.d 0 5) (by simp) with h2170 | h2170
                                          · linarith only [h1, h2170, hlam]
                                          · linarith only [h2098, h2170, hlam]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          rcases p2161_3 (m.d 0 5) (by simp) with h2173 | h2173
                                          · linarith only [h1, h2173, hlam]
                                          · linarith only [h2099, h2173, hlam]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h0, h1, h2107, h2109, hc12, hc23, hlam, hphi, p2161_1]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h0, h1, h2107, h2109, hc12, hc23, hlam, hphi, p2161_1]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          rcases p2161_3 (m.d 0 5) (by simp) with h2179 | h2179
                                          · linarith only [h2096, h2179, hlam]
                                          · linarith only [h2098, h2179, hlam]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          rcases p2161_3 (m.d 0 5) (by simp) with h2182 | h2182
                                          · linarith only [h2096, h2182, hlam]
                                          · linarith only [h2099, h2182, hlam]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h2098, hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h0, h1, hc12, hc35, hlam, hphi, ht23, p2161_1]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h2108, hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h2098, hc45, hlam, hphi, ht0b, ht5b, p2161_1, u0elo4]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h2099, hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h2106, hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h2109, hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [h2110, hlam, p2161_0]
                                        · have p2161_0 := h2161c.1
                                          have p2161_1 := h2161c.2.1
                                          have p2161_2 := h2161c.2.2.1
                                          have p2161_3 := h2161c.2.2.2
                                          linarith only [hlam, p2161_0]
                                      · linarith only [h2160, hlam, p2111_0]
                                    · linarith only [h2070, h2159, hlam]
                                  · linarith only [h2026, h2158, hlam]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              rcases p2111_3 (m.d 0 2) (by simp) with h2198 | h2198
                              · linarith only [h2096, h2198, hlam]
                              · linarith only [h0, h2198, hlam]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h2108, hlam, p2111_1]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [h2109, hlam, p2111_0]
                            · have p2111_0 := h2111c.1
                              have p2111_1 := h2111c.2.1
                              have p2111_2 := h2111c.2.2.1
                              have p2111_3 := h2111c.2.2.2
                              linarith only [hlam, p2111_0]
                          · rcases h2bigk with h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h2026, hc12, hc23, hlam, hphi, p2204_1]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h2026, hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h2070, hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h2096, hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h0, hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h2100, hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h2102, hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h2104, hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              rcases p2204_3 (m.d 0 2) (by simp) with h2215 | h2215
                              · linarith only [h2215, hlam, p2204_0]
                              · rcases p2204_3 (m.d 1 2) (by simp) with h2217 | h2217
                                · linarith only [h2100, h2217, hlam]
                                · rcases p2204_3 (m.d 2 3) (by simp) with h2219 | h2219
                                  · rcases p2204_3 (m.d 2 4) (by simp) with h2220 | h2220
                                    · linarith only [h2107, h2220, hlam]
                                    · linarith only [h2070, h2220, hlam]
                                  · linarith only [h2219, hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              rcases p2204_3 (m.d 0 2) (by simp) with h2224 | h2224
                              · linarith only [h2026, h2224, hlam]
                              · linarith only [h0, h2224, hlam]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h2070, hc02, hc23, hlam, hphi, p2204_1]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h0, h1, h2104, hc12, hc23, hlam, hphi, p2204_1]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              rcases p2204_3 (m.d 0 2) (by simp) with h2230 | h2230
                              · linarith only [h2230, hlam, p2204_0]
                              · rcases p2204_3 (m.d 1 2) (by simp) with h2232 | h2232
                                · linarith only [h2102, h2232, hlam]
                                · rcases p2204_3 (m.d 2 3) (by simp) with h2234 | h2234
                                  · rcases p2204_3 (m.d 2 4) (by simp) with h2235 | h2235
                                    · rcases p2204_3 (m.d 2 5) (by simp) with h2236 | h2236
                                      · linarith only [h2109, h2236, hlam]
                                      · linarith only [h2096, h2236, hlam]
                                    · linarith only [h2235, hlam, p2204_0]
                                  · linarith only [h2026, h2234, hlam]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              rcases p2204_3 (m.d 0 2) (by simp) with h2241 | h2241
                              · linarith only [h2070, h2241, hlam]
                              · linarith only [h0, h2241, hlam]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h2107, hlam, p2204_1]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h0, h1, h2104, hc12, hc24, hlam, hphi, p2204_1]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              rcases p2204_3 (m.d 0 2) (by simp) with h2247 | h2247
                              · linarith only [h2247, hlam, p2204_0]
                              · rcases p2204_3 (m.d 1 2) (by simp) with h2249 | h2249
                                · linarith only [h2104, h2249, hlam]
                                · rcases p2204_3 (m.d 2 3) (by simp) with h2251 | h2251
                                  · rcases p2204_3 (m.d 2 4) (by simp) with h2252 | h2252
                                    · rcases p2204_3 (m.d 2 5) (by simp) with h2253 | h2253
                                      · rcases h5bigk with h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c | h2254c
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [hlam, p2254_0]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h1, hlam, p2254_1]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2096, hlam, p2254_0]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [hc35, hlam, hphi, ht0b, ht5b, p2254_1, u0elo4]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2099, h2110, hc34, hlam, hphi, ht0b, ht45, ht5b, p2254_1, u0elo3]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h0, h1, h2104, hc12, hc25, hlam, hphi, p2254_1]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [hlam, p2254_0]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2104, hlam, p2254_0]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          rcases p2254_3 (m.d 0 5) (by simp) with h2263 | h2263
                                          · linarith only [h1, h2263, hlam]
                                          · linarith only [h2098, h2263, hlam]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2102, h2106, h2107, h2110, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2254_1]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h0, h1, h2107, h2109, hc12, hc23, hlam, hphi, p2254_1]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h0, h1, h2107, h2109, hc12, hc23, hlam, hphi, p2254_1]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [hlam, p2254_0]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          rcases p2254_3 (m.d 0 5) (by simp) with h2270 | h2270
                                          · linarith only [h2096, h2270, hlam]
                                          · linarith only [h2098, h2270, hlam]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2107, h2109, h2110, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2254_1]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2098, hlam, p2254_0]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h0, h1, hc12, hc35, hlam, hphi, ht23, p2254_1]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2108, hlam, p2254_0]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [hlam, p2254_0]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2110, hlam, p2254_1]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2099, hlam, p2254_0]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2106, hlam, p2254_0]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2109, hlam, p2254_0]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [h2099, hc35, hlam, hphi, ht0b, ht5b, p2254_1, u0elo3]
                                        · have p2254_0 := h2254c.1
                                          have p2254_1 := h2254c.2.1
                                          have p2254_2 := h2254c.2.2.1
                                          have p2254_3 := h2254c.2.2.2
                                          linarith only [hlam, p2254_0]
                                      · linarith only [h2253, hlam, p2204_0]
                                    · linarith only [h2070, h2252, hlam]
                                  · linarith only [h2026, h2251, hlam]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              rcases p2204_3 (m.d 0 2) (by simp) with h2287 | h2287
                              · linarith only [h2096, h2287, hlam]
                              · linarith only [h0, h2287, hlam]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h2108, hlam, p2204_1]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [h2109, hlam, p2204_0]
                            · have p2204_0 := h2204c.1
                              have p2204_1 := h2204c.2.1
                              have p2204_2 := h2204c.2.2.1
                              have p2204_3 := h2204c.2.2.2
                              linarith only [hlam, p2204_0]
                        · linarith only [h2070, h2099, h2109, hlam]
                      · linarith only [h0, h1, h2102, h2106, h2107, h2108, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2295 | h2295
                      · linarith only [h0, h1, h2104, h2107, h2295, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h2026, h2098, h2295, hlam]
                  · linarith only [h0, h1, h2099, h2106, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2299 | h2299
            · linarith only [h0, h2026, h2098, h2299, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2301 | h2301
              · linarith only [h0, h2070, h2301, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2303 | h2303
                · linarith only [h0, h1, h2096, h2303, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2305 | h2305
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2306 | h2306
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2307 | h2307
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2308 | h2308
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2309 | h2309
                          · linarith only [h2070, h2099, h2306, h2309, hc02, hc23, hlam, hphi]
                          · rcases h2bigk with h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h2070, h2099, hc12, hc45, hlam, hphi, ht23, ht34, p2311_1]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h2026, hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h2070, hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h2096, hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h0, hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h2299, hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h2301, hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h2303, hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              rcases p2311_3 (m.d 0 2) (by simp) with h2322 | h2322
                              · linarith only [h2322, hlam, p2311_0]
                              · rcases p2311_3 (m.d 1 2) (by simp) with h2324 | h2324
                                · linarith only [h2299, h2324, hlam]
                                · rcases p2311_3 (m.d 2 3) (by simp) with h2326 | h2326
                                  · rcases p2311_3 (m.d 2 4) (by simp) with h2327 | h2327
                                    · linarith only [h2306, h2327, hlam]
                                    · linarith only [h2070, h2327, hlam]
                                  · linarith only [h2326, hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              rcases p2311_3 (m.d 0 2) (by simp) with h2331 | h2331
                              · linarith only [h2026, h2331, hlam]
                              · linarith only [h0, h2331, hlam]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h2070, h2099, h2301, h2305, hc02, hc23, hlam, hphi, p2311_1]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h0, h1, h2303, hc12, hc23, hlam, hphi, p2311_1]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              rcases p2311_3 (m.d 0 2) (by simp) with h2337 | h2337
                              · linarith only [h2337, hlam, p2311_0]
                              · rcases p2311_3 (m.d 1 2) (by simp) with h2339 | h2339
                                · linarith only [h2301, h2339, hlam]
                                · rcases p2311_3 (m.d 2 3) (by simp) with h2341 | h2341
                                  · rcases p2311_3 (m.d 2 4) (by simp) with h2342 | h2342
                                    · rcases p2311_3 (m.d 2 5) (by simp) with h2343 | h2343
                                      · linarith only [h2308, h2343, hlam]
                                      · linarith only [h2096, h2343, hlam]
                                    · linarith only [h2342, hlam, p2311_0]
                                  · linarith only [h2026, h2341, hlam]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              rcases p2311_3 (m.d 0 2) (by simp) with h2348 | h2348
                              · linarith only [h2070, h2348, hlam]
                              · linarith only [h0, h2348, hlam]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h2306, hlam, p2311_1]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h0, h1, h2303, hc12, hc24, hlam, hphi, p2311_1]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              rcases p2311_3 (m.d 0 2) (by simp) with h2354 | h2354
                              · linarith only [h2354, hlam, p2311_0]
                              · rcases p2311_3 (m.d 1 2) (by simp) with h2356 | h2356
                                · linarith only [h2303, h2356, hlam]
                                · rcases p2311_3 (m.d 2 3) (by simp) with h2358 | h2358
                                  · rcases p2311_3 (m.d 2 4) (by simp) with h2359 | h2359
                                    · rcases p2311_3 (m.d 2 5) (by simp) with h2360 | h2360
                                      · rcases h5bigk with h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [hlam, p2361_0]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h1, hlam, p2361_1]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h2096, hlam, p2361_0]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [hc35, hlam, hphi, ht0b, ht5b, p2361_1, u0elo4]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h2099, hlam, p2361_1]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h0, h1, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2361_1]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [hlam, p2361_0]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h2303, hlam, p2361_0]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          rcases p2361_3 (m.d 0 5) (by simp) with h2370 | h2370
                                          · linarith only [h1, h2370, hlam]
                                          · linarith only [h2098, h2370, hlam]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h0, h2070, h2099, h2301, h2305, h2306, hc12, hc23, hlam, hphi, p2361_1]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h0, h1, h2306, h2308, hc12, hc23, hlam, hphi, p2361_1]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h0, h1, h2306, h2308, hc12, hc23, hlam, hphi, p2361_1]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [hlam, p2361_0]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          rcases p2361_3 (m.d 0 5) (by simp) with h2377 | h2377
                                          · linarith only [h2096, h2377, hlam]
                                          · linarith only [h2098, h2377, hlam]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h0, h2070, h2099, h2306, h2308, hc12, hc23, hlam, hphi, p2361_1]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h2098, hlam, p2361_0]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h0, h1, hc12, hc35, hlam, hphi, ht23, p2361_1]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h2307, hlam, p2361_0]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [hlam, p2361_0]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h2309, hlam, p2361_1]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h0, h1, hc12, hc45, hlam, hphi, ht23, ht34, p2361_1]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h2305, hlam, p2361_0]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h2308, hlam, p2361_0]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [h2301, h2305, h2306, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2361_1]
                                        · have p2361_0 := h2361c.1
                                          have p2361_1 := h2361c.2.1
                                          have p2361_2 := h2361c.2.2.1
                                          have p2361_3 := h2361c.2.2.2
                                          linarith only [hlam, p2361_0]
                                      · linarith only [h2360, hlam, p2311_0]
                                    · linarith only [h2070, h2359, hlam]
                                  · linarith only [h2026, h2358, hlam]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              rcases p2311_3 (m.d 0 2) (by simp) with h2394 | h2394
                              · linarith only [h2096, h2394, hlam]
                              · linarith only [h0, h2394, hlam]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h2307, hlam, p2311_1]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [h2308, hlam, p2311_0]
                            · have p2311_0 := h2311c.1
                              have p2311_1 := h2311c.2.1
                              have p2311_2 := h2311c.2.2.1
                              have p2311_3 := h2311c.2.2.2
                              linarith only [hlam, p2311_0]
                        · linarith only [h2301, h2305, h2308, hlam]
                      · linarith only [h2026, h2098, h2307, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2402 | h2402
                      · linarith only [h0, h1, h2303, h2306, h2402, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h2026, h2098, h2402, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2405 | h2405
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2406 | h2406
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2407 | h2407
                        · linarith only [h0, h1, h2305, h2407, hc12, hc24, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2409 | h2409
                          · linarith only [h2405, h2407, h2409, hlam]
                          · rcases h2bigk with h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c | h2411c
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h0, h1, h2303, hc12, hc25, hlam, hphi, p2411_1]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h2026, hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h2070, hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h2096, hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h0, hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h2299, hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h2301, hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h2303, hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              rcases p2411_3 (m.d 0 2) (by simp) with h2422 | h2422
                              · linarith only [h2422, hlam, p2411_0]
                              · rcases p2411_3 (m.d 1 2) (by simp) with h2424 | h2424
                                · linarith only [h2299, h2424, hlam]
                                · rcases p2411_3 (m.d 2 3) (by simp) with h2426 | h2426
                                  · rcases p2411_3 (m.d 2 4) (by simp) with h2427 | h2427
                                    · linarith only [h2405, h2427, hlam]
                                    · linarith only [h2070, h2427, hlam]
                                  · linarith only [h2426, hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              rcases p2411_3 (m.d 0 2) (by simp) with h2431 | h2431
                              · linarith only [h2026, h2431, hlam]
                              · linarith only [h0, h2431, hlam]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h2070, hc02, hc23, hlam, hphi, p2411_1]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h0, h1, h2303, hc12, hc23, hlam, hphi, p2411_1]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h0, h2407, hc12, hc45, hlam, hphi, ht23, ht34, p2411_1]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h2407, hc12, hc45, hlam, hphi, ht23, ht34, p2411_1]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h2405, hlam, p2411_1]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [hlam, p2411_0]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h2407, hlam, p2411_1]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              rcases p2411_3 (m.d 0 2) (by simp) with h2442 | h2442
                              · linarith only [h2442, hlam, p2411_0]
                              · rcases p2411_3 (m.d 1 2) (by simp) with h2444 | h2444
                                · linarith only [h2303, h2444, hlam]
                                · rcases p2411_3 (m.d 2 3) (by simp) with h2446 | h2446
                                  · rcases p2411_3 (m.d 2 4) (by simp) with h2447 | h2447
                                    · linarith only [h2407, h2447, hlam]
                                    · linarith only [h2070, h2447, hlam]
                                  · linarith only [h2026, h2446, hlam]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              rcases p2411_3 (m.d 0 2) (by simp) with h2451 | h2451
                              · linarith only [h2096, h2451, hlam]
                              · linarith only [h0, h2451, hlam]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h2406, hlam, p2411_1]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [h0, h2070, hc12, hc25, hlam, hphi, p2411_1]
                            · have p2411_0 := h2411c.1
                              have p2411_1 := h2411c.2.1
                              have p2411_2 := h2411c.2.2.1
                              have p2411_3 := h2411c.2.2.2
                              linarith only [hlam, p2411_0]
                      · linarith only [h2026, h2098, h2406, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2458 | h2458
                      · linarith only [h0, h1, h2303, h2405, h2458, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h2026, h2098, h2458, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2461 | h2461
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2462 | h2462
            · linarith only [h0, h2026, h2462, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2464 | h2464
              · linarith only [h0, h1, h2070, h2461, h2464, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2466 | h2466
                · linarith only [h0, h2096, h2466, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2468 | h2468
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2469 | h2469
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2470 | h2470
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2471 | h2471
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2472 | h2472
                          · rcases h2bigk with h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h0, h1, h2464, h2468, hc12, hc24, hlam, hphi, p2473_1]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h2026, hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h2070, hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h2096, hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h0, hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h2462, hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h2464, hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h2466, hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              rcases p2473_3 (m.d 0 2) (by simp) with h2484 | h2484
                              · linarith only [h2484, hlam, p2473_0]
                              · rcases p2473_3 (m.d 1 2) (by simp) with h2486 | h2486
                                · linarith only [h2462, h2486, hlam]
                                · rcases p2473_3 (m.d 2 3) (by simp) with h2488 | h2488
                                  · rcases p2473_3 (m.d 2 4) (by simp) with h2489 | h2489
                                    · linarith only [h2469, h2489, hlam]
                                    · linarith only [h2070, h2489, hlam]
                                  · linarith only [h2488, hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              rcases p2473_3 (m.d 0 2) (by simp) with h2493 | h2493
                              · linarith only [h2026, h2493, hlam]
                              · linarith only [h0, h2493, hlam]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h1, h2464, h2468, hc01, hc23, hlam, hphi, ht12, p2473_1]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h0, h1, h2466, hc12, hc23, hlam, hphi, p2473_1]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              rcases p2473_3 (m.d 0 2) (by simp) with h2499 | h2499
                              · linarith only [h2499, hlam, p2473_0]
                              · rcases p2473_3 (m.d 1 2) (by simp) with h2501 | h2501
                                · linarith only [h2464, h2501, hlam]
                                · rcases p2473_3 (m.d 2 3) (by simp) with h2503 | h2503
                                  · rcases p2473_3 (m.d 2 4) (by simp) with h2504 | h2504
                                    · rcases p2473_3 (m.d 2 5) (by simp) with h2505 | h2505
                                      · linarith only [h2471, h2505, hlam]
                                      · linarith only [h2096, h2505, hlam]
                                    · linarith only [h2504, hlam, p2473_0]
                                  · linarith only [h2026, h2503, hlam]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              rcases p2473_3 (m.d 0 2) (by simp) with h2510 | h2510
                              · linarith only [h2070, h2510, hlam]
                              · linarith only [h0, h2510, hlam]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h2469, hlam, p2473_1]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h0, h1, h2466, hc12, hc24, hlam, hphi, p2473_1]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              rcases p2473_3 (m.d 0 2) (by simp) with h2516 | h2516
                              · linarith only [h2516, hlam, p2473_0]
                              · rcases p2473_3 (m.d 1 2) (by simp) with h2518 | h2518
                                · linarith only [h2466, h2518, hlam]
                                · rcases p2473_3 (m.d 2 3) (by simp) with h2520 | h2520
                                  · rcases p2473_3 (m.d 2 4) (by simp) with h2521 | h2521
                                    · rcases p2473_3 (m.d 2 5) (by simp) with h2522 | h2522
                                      · rcases h5bigk with h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c | h2523c
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [hlam, p2523_0]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h1, hlam, p2523_1]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h2096, hlam, p2523_0]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h2098, hlam, p2523_1]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h2098, h2469, h2472, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2523_1]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h0, h1, h2468, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2523_1]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [hlam, p2523_0]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h2466, hlam, p2523_0]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h2026, h2098, h2464, h2468, h2469, hc02, hc23, hlam, hphi, p2523_1]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          rcases p2523_3 (m.d 0 5) (by simp) with h2533 | h2533
                                          · linarith only [h1, h2533, hlam]
                                          · linarith only [h2461, h2533, hlam]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h0, h1, hc12, hc25, hlam, hphi, p2523_1]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h0, h1, hc12, hc25, hlam, hphi, p2523_1]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [hlam, p2523_0]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h0, h2026, h2098, h2470, hc12, hc23, hlam, hphi, p2523_1]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          rcases p2523_3 (m.d 0 5) (by simp) with h2540 | h2540
                                          · linarith only [h2096, h2540, hlam]
                                          · linarith only [h2461, h2540, hlam]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h0, h1, hc12, hc35, hlam, hphi, ht23, p2523_1]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h0, h1, h2469, h2472, hc12, hc23, hlam, hphi, p2523_1]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h2470, hlam, p2523_0]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [hlam, p2523_0]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h2469, h2472, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2523_1]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h2461, hlam, p2523_0]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h2468, hlam, p2523_0]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h2471, hlam, p2523_0]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [h2472, hlam, p2523_0]
                                        · have p2523_0 := h2523c.1
                                          have p2523_1 := h2523c.2.1
                                          have p2523_2 := h2523c.2.2.1
                                          have p2523_3 := h2523c.2.2.2
                                          linarith only [hlam, p2523_0]
                                      · linarith only [h2522, hlam, p2473_0]
                                    · linarith only [h2070, h2521, hlam]
                                  · linarith only [h2026, h2520, hlam]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              rcases p2473_3 (m.d 0 2) (by simp) with h2556 | h2556
                              · linarith only [h2096, h2556, hlam]
                              · linarith only [h0, h2556, hlam]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h2470, hlam, p2473_1]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [h2471, hlam, p2473_0]
                            · have p2473_0 := h2473c.1
                              have p2473_1 := h2473c.2.1
                              have p2473_2 := h2473c.2.2.1
                              have p2473_3 := h2473c.2.2.2
                              linarith only [hlam, p2473_0]
                          · linarith only [h2098, h2461, h2472, hlam]
                        · linarith only [h0, h2070, h2461, h2471, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1, h2464, h2468, h2469, h2470, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2565 | h2565
                      · linarith only [h0, h2026, h2098, h2469, h2565, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2567 | h2567
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2568 | h2568
                          · rcases h2bigk with h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c | h2569c
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h0, h1, h2464, h2468, hc12, hc24, hlam, hphi, p2569_1]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h2026, hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h2070, hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h2096, hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h0, hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h2462, hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h2464, hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h2466, hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h2565, h2568, hc02, hc34, hlam, hphi, ht23, p2569_1]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h2565, h2568, hc12, hc34, hlam, hphi, ht23, p2569_1]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h2469, hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h2565, hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              rcases p2569_3 (m.d 0 2) (by simp) with h2585 | h2585
                              · linarith only [h2585, hlam, p2569_0]
                              · rcases p2569_3 (m.d 1 2) (by simp) with h2587 | h2587
                                · linarith only [h2464, h2587, hlam]
                                · rcases p2569_3 (m.d 2 3) (by simp) with h2589 | h2589
                                  · linarith only [h2469, h2589, hlam]
                                  · linarith only [h2026, h2589, hlam]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              rcases p2569_3 (m.d 0 2) (by simp) with h2592 | h2592
                              · linarith only [h2070, h2592, hlam]
                              · linarith only [h0, h2592, hlam]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h0, h2026, h2469, hc12, hc34, hlam, hphi, ht23, p2569_1]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h0, h2096, h2469, hc12, hc34, hlam, hphi, ht23, p2569_1]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              rcases p2569_3 (m.d 0 2) (by simp) with h2598 | h2598
                              · linarith only [h2598, hlam, p2569_0]
                              · rcases p2569_3 (m.d 1 2) (by simp) with h2600 | h2600
                                · linarith only [h2466, h2600, hlam]
                                · rcases p2569_3 (m.d 2 3) (by simp) with h2602 | h2602
                                  · linarith only [h2565, h2602, hlam]
                                  · linarith only [h2026, h2602, hlam]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              rcases p2569_3 (m.d 0 2) (by simp) with h2605 | h2605
                              · linarith only [h2096, h2605, hlam]
                              · linarith only [h0, h2605, hlam]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h0, h2026, hc12, hc25, hlam, hphi, p2569_1]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [h2567, hlam, p2569_0]
                            · have p2569_0 := h2569c.1
                              have p2569_1 := h2569c.2.1
                              have p2569_2 := h2569c.2.2.1
                              have p2569_3 := h2569c.2.2.2
                              linarith only [hlam, p2569_0]
                          · linarith only [h1, h2461, h2464, h2468, h2469, h2568, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h2070, h2461, h2567, hlam]
                  · linarith only [h0, h1, h2461, h2468, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2614 | h2614
            · linarith only [h0, h2026, h2614, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2616 | h2616
              · linarith only [h0, h2070, h2616, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2618 | h2618
                · linarith only [h0, h1, h2096, h2618, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2620 | h2620
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2621 | h2621
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2622 | h2622
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2623 | h2623
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2624 | h2624
                          · linarith only [h0, h2070, h2461, h2621, h2624, hc12, hc23, hlam, hphi]
                          · rcases h2bigk with h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2026, h2098, h2620, h2624, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2026, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2070, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2096, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h0, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2614, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2616, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2618, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 2) (by simp) with h2637 | h2637
                              · linarith only [h2637, hlam, p2626_0]
                              · rcases p2626_3 (m.d 1 2) (by simp) with h2639 | h2639
                                · linarith only [h2614, h2639, hlam]
                                · rcases p2626_3 (m.d 2 3) (by simp) with h2641 | h2641
                                  · rcases p2626_3 (m.d 2 4) (by simp) with h2642 | h2642
                                    · linarith only [h2621, h2642, hlam]
                                    · linarith only [h2070, h2642, hlam]
                                  · linarith only [h2641, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 2) (by simp) with h2646 | h2646
                              · linarith only [h2026, h2646, hlam]
                              · linarith only [h0, h2646, hlam]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2026, h2098, h2616, h2620, h2624, hc02, hc23, hlam, hphi, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h0, h1, h2618, hc12, hc23, hlam, hphi, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 2) (by simp) with h2652 | h2652
                              · linarith only [h2652, hlam, p2626_0]
                              · rcases p2626_3 (m.d 1 2) (by simp) with h2654 | h2654
                                · linarith only [h2616, h2654, hlam]
                                · rcases p2626_3 (m.d 2 3) (by simp) with h2656 | h2656
                                  · rcases p2626_3 (m.d 2 4) (by simp) with h2657 | h2657
                                    · rcases p2626_3 (m.d 2 5) (by simp) with h2658 | h2658
                                      · linarith only [h2623, h2658, hlam]
                                      · linarith only [h2096, h2658, hlam]
                                    · linarith only [h2657, hlam, p2626_0]
                                  · linarith only [h2026, h2656, hlam]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 2) (by simp) with h2663 | h2663
                              · linarith only [h2070, h2663, hlam]
                              · linarith only [h0, h2663, hlam]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2621, hlam, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h0, h1, h2618, hc12, hc24, hlam, hphi, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 2) (by simp) with h2669 | h2669
                              · linarith only [h2669, hlam, p2626_0]
                              · rcases p2626_3 (m.d 1 2) (by simp) with h2671 | h2671
                                · linarith only [h2618, h2671, hlam]
                                · rcases p2626_3 (m.d 2 3) (by simp) with h2673 | h2673
                                  · rcases p2626_3 (m.d 2 4) (by simp) with h2674 | h2674
                                    · rcases p2626_3 (m.d 2 5) (by simp) with h2675 | h2675
                                      · rcases h5bigk with h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [hlam, p2676_0]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h1, hlam, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h2096, hlam, p2676_0]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h2098, hlam, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h2461, hlam, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h0, h1, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [hlam, p2676_0]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h2618, hlam, p2676_0]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h0, h2026, h2098, h2616, h2620, h2621, hc12, hc23, hlam, hphi, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h0, h2026, h2098, h2616, h2620, h2621, h2624, hc12, hc23, hlam, hphi, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h0, h1, h2621, h2623, hc12, hc23, hlam, hphi, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h0, h1, h2621, h2623, hc12, hc23, hlam, hphi, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [hlam, p2676_0]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h0, h2026, h2098, h2621, h2623, hc12, hc23, hlam, hphi, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h0, h2026, h2098, h2621, h2623, h2624, hc12, hc23, hlam, hphi, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h0, h1, hc12, hc35, hlam, hphi, ht23, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h0, h1, h2616, h2620, h2621, h2624, hc12, hc23, hlam, hphi, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h2622, hlam, p2676_0]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [hlam, p2676_0]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h2624, hlam, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h0, h1, h2616, h2620, h2621, hc12, hc23, hlam, hphi, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h2620, hlam, p2676_0]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h2623, hlam, p2676_0]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [h2616, h2620, h2621, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2676_1]
                                        · have p2676_0 := h2676c.1
                                          have p2676_1 := h2676c.2.1
                                          have p2676_2 := h2676c.2.2.1
                                          have p2676_3 := h2676c.2.2.2
                                          linarith only [hlam, p2676_0]
                                      · linarith only [h2675, hlam, p2626_0]
                                    · linarith only [h2070, h2674, hlam]
                                  · linarith only [h2026, h2673, hlam]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              rcases p2626_3 (m.d 0 2) (by simp) with h2705 | h2705
                              · linarith only [h2096, h2705, hlam]
                              · linarith only [h0, h2705, hlam]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2622, hlam, p2626_1]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [h2623, hlam, p2626_0]
                            · have p2626_0 := h2626c.1
                              have p2626_1 := h2626c.2.1
                              have p2626_2 := h2626c.2.2.1
                              have p2626_3 := h2626c.2.2.2
                              linarith only [hlam, p2626_0]
                        · linarith only [h2616, h2620, h2623, hlam]
                      · linarith only [h0, h2070, h2461, h2616, h2620, h2621, h2622, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2713 | h2713
                      · linarith only [h0, h2026, h2098, h2621, h2713, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2715 | h2715
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2716 | h2716
                          · rcases h2bigk with h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2070, h2461, h2620, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2717_1]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2026, hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2070, hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2096, hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h0, hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2614, hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2616, hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2618, hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2713, h2716, hc02, hc34, hlam, hphi, ht23, p2717_1]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2713, h2716, hc12, hc34, hlam, hphi, ht23, p2717_1]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2621, hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2713, hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              rcases p2717_3 (m.d 0 2) (by simp) with h2733 | h2733
                              · linarith only [h2733, hlam, p2717_0]
                              · rcases p2717_3 (m.d 1 2) (by simp) with h2735 | h2735
                                · linarith only [h2616, h2735, hlam]
                                · rcases p2717_3 (m.d 2 3) (by simp) with h2737 | h2737
                                  · linarith only [h2621, h2737, hlam]
                                  · linarith only [h2026, h2737, hlam]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              rcases p2717_3 (m.d 0 2) (by simp) with h2740 | h2740
                              · linarith only [h2070, h2740, hlam]
                              · linarith only [h0, h2740, hlam]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h0, h2026, h2621, hc12, hc34, hlam, hphi, ht23, p2717_1]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h0, h2096, h2621, hc12, hc34, hlam, hphi, ht23, p2717_1]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              rcases p2717_3 (m.d 0 2) (by simp) with h2746 | h2746
                              · linarith only [h2746, hlam, p2717_0]
                              · rcases p2717_3 (m.d 1 2) (by simp) with h2748 | h2748
                                · linarith only [h2618, h2748, hlam]
                                · rcases p2717_3 (m.d 2 3) (by simp) with h2750 | h2750
                                  · linarith only [h2713, h2750, hlam]
                                  · linarith only [h2026, h2750, hlam]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              rcases p2717_3 (m.d 0 2) (by simp) with h2753 | h2753
                              · linarith only [h2096, h2753, hlam]
                              · linarith only [h0, h2753, hlam]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h0, h2026, hc12, hc25, hlam, hphi, p2717_1]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [h2715, hlam, p2717_0]
                            · have p2717_0 := h2717c.1
                              have p2717_1 := h2717c.2.1
                              have p2717_2 := h2717c.2.2.1
                              have p2717_3 := h2717c.2.2.2
                              linarith only [hlam, p2717_0]
                          · linarith only [h2616, h2620, h2621, h2716, hlam]
                        · linarith only [h2616, h2620, h2715, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2761 | h2761
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2762 | h2762
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2763 | h2763
                        · linarith only [h0, h1, h2620, h2763, hc12, hc24, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2765 | h2765
                          · linarith only [h2761, h2763, h2765, hlam]
                          · rcases h2bigk with h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c | h2767c
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2026, h2098, h2762, hc12, hc23, hlam, hphi, p2767_1]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2026, hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2070, hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2096, hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h0, hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2614, hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2616, hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2618, hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              rcases p2767_3 (m.d 0 2) (by simp) with h2778 | h2778
                              · linarith only [h2778, hlam, p2767_0]
                              · rcases p2767_3 (m.d 1 2) (by simp) with h2780 | h2780
                                · linarith only [h2614, h2780, hlam]
                                · rcases p2767_3 (m.d 2 3) (by simp) with h2782 | h2782
                                  · rcases p2767_3 (m.d 2 4) (by simp) with h2783 | h2783
                                    · linarith only [h2761, h2783, hlam]
                                    · linarith only [h2070, h2783, hlam]
                                  · linarith only [h2782, hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              rcases p2767_3 (m.d 0 2) (by simp) with h2787 | h2787
                              · linarith only [h2026, h2787, hlam]
                              · linarith only [h0, h2787, hlam]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2070, hc02, hc23, hlam, hphi, p2767_1]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h0, h1, h2618, hc12, hc23, hlam, hphi, p2767_1]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h0, h2763, hc12, hc45, hlam, hphi, ht23, ht34, p2767_1]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2763, hc12, hc45, hlam, hphi, ht23, ht34, p2767_1]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2761, hlam, p2767_1]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [hlam, p2767_0]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2763, hlam, p2767_1]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              rcases p2767_3 (m.d 0 2) (by simp) with h2798 | h2798
                              · linarith only [h2798, hlam, p2767_0]
                              · rcases p2767_3 (m.d 1 2) (by simp) with h2800 | h2800
                                · linarith only [h2618, h2800, hlam]
                                · rcases p2767_3 (m.d 2 3) (by simp) with h2802 | h2802
                                  · rcases p2767_3 (m.d 2 4) (by simp) with h2803 | h2803
                                    · linarith only [h2763, h2803, hlam]
                                    · linarith only [h2070, h2803, hlam]
                                  · linarith only [h2026, h2802, hlam]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              rcases p2767_3 (m.d 0 2) (by simp) with h2807 | h2807
                              · linarith only [h2096, h2807, hlam]
                              · linarith only [h0, h2807, hlam]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h2762, hlam, p2767_1]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [h0, h2070, hc12, hc25, hlam, hphi, p2767_1]
                            · have p2767_0 := h2767c.1
                              have p2767_1 := h2767c.2.1
                              have p2767_2 := h2767c.2.2.1
                              have p2767_3 := h2767c.2.2.2
                              linarith only [hlam, p2767_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2813 | h2813
                        · linarith only [h0, h1, h2620, h2761, h2813, hc12, hc23, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2815 | h2815
                          · linarith only [h0, h1, h2618, h2761, h2762, h2813, h2815, hc12, hc35, hlam, hphi, ht23]
                          · rcases h2bigk with h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2070, h2761, hc12, hc23, hlam, hphi, p2817_1]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2026, hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2070, hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2096, hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h0, hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2614, hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2616, hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2618, hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2762, h2815, hc02, hc45, hlam, hphi, ht23, ht34, p2817_1]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2762, h2815, hc12, hc45, hlam, hphi, ht23, ht34, p2817_1]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2616, h2762, h2815, hc14, hc45, hlam, hphi, p2817_1]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2762, hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h0, h2761, h2762, h2815, hc12, hc45, hlam, hphi, ht23, ht34, p2817_1]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2761, h2762, h2815, hc12, hc45, hlam, hphi, ht23, ht34, p2817_1]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2761, hlam, p2817_1]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [hlam, p2817_0]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h2813, hlam, p2817_1]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              rcases p2817_3 (m.d 0 2) (by simp) with h2838 | h2838
                              · linarith only [h2838, hlam, p2817_0]
                              · rcases p2817_3 (m.d 1 2) (by simp) with h2840 | h2840
                                · linarith only [h2618, h2840, hlam]
                                · rcases p2817_3 (m.d 2 3) (by simp) with h2842 | h2842
                                  · linarith only [h2762, h2842, hlam]
                                  · linarith only [h2026, h2842, hlam]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              rcases p2817_3 (m.d 0 2) (by simp) with h2845 | h2845
                              · linarith only [h2096, h2845, hlam]
                              · linarith only [h0, h2845, hlam]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h0, h2026, hc12, hc25, hlam, hphi, p2817_1]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [h0, h2070, h2762, h2815, hc12, hc45, hlam, hphi, ht23, ht34, p2817_1]
                            · have p2817_0 := h2817c.1
                              have p2817_1 := h2817c.2.1
                              have p2817_2 := h2817c.2.2.1
                              have p2817_3 := h2817c.2.2.2
                              linarith only [hlam, p2817_0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2851 | h2851
                      · linarith only [h2098, h2761, h2851, hc03, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2853 | h2853
                        · linarith only [h0, h1, h2620, h2853, hc12, hc24, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2855 | h2855
                          · linarith only [h0, h2070, h2853, h2855, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h2026, h2761, h2855, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
