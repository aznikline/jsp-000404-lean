import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2108 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2109 | h2109
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2110 | h2110
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2111 | h2111
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2112 | h2112
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2113 | h2113
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2114 | h2114
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2115 | h2115
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2116 | h2116
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2117 | h2117
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2118 | h2118
                    · linarith only [h0, h2108, h2118, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h2108, h2113, h2115, h2118, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2117, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2108, h2115, h2116, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2108, h2115, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2124 | h2124
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2125 | h2125
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2126 | h2126
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2127 | h2127
                    · linarith only [h0, h2108, h2127, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h2108, h2113, h2127, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2126, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2108, h2124, h2125, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2108, h2124, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2133 | h2133
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2134 | h2134
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2135 | h2135
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2136 | h2136
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2137 | h2137
                    · linarith only [h0, h2108, h2113, h2137, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2139 | h2139
                      · linarith only [h0, h2109, h2137, h2139, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2141 | h2141
                        · linarith only [h0, h2109, h2141, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h0, h2109, h2133, h2137, h2141, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2136, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2108, h2134, h2135, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2108, h2134, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2147 | h2147
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2148 | h2148
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2149 | h2149
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2150 | h2150
                    · linarith only [h0, h2108, h2150, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2152 | h2152
                      · linarith only [h0, h2109, h2150, h2152, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2154 | h2154
                        · linarith only [h0, h2109, h2113, h2133, h2154, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2156 | h2156
                          · linarith only [h2108, h2113, h2147, h2156, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2158 | h2158
                            · linarith only [h0, h2111, h2152, h2158, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2160 | h2160
                              · linarith only [h2112, h2133, h2160, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2162 | h2162
                                · rcases h2bigk with h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h0, hlam, p2163_1]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    rcases p2163_3 (m.d 0 2) (by simp) with h2166 | h2166
                                    · rcases p2163_3 (m.d 1 2) (by simp) with h2167 | h2167
                                      · rcases p2163_3 (m.d 2 3) (by simp) with h2168 | h2168
                                        · linarith only [h2168, hlam, p2163_0]
                                        · rcases p2163_3 (m.d 2 4) (by simp) with h2170 | h2170
                                          · linarith only [h2112, h2170, hlam]
                                          · linarith only [h2156, h2170, hlam]
                                      · linarith only [h2147, h2167, hlam]
                                    · linarith only [h2166, hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    rcases p2163_3 (m.d 0 2) (by simp) with h2175 | h2175
                                    · rcases p2163_3 (m.d 1 2) (by simp) with h2176 | h2176
                                      · rcases p2163_3 (m.d 2 3) (by simp) with h2177 | h2177
                                        · linarith only [h2111, h2177, hlam]
                                        · rcases p2163_3 (m.d 2 4) (by simp) with h2179 | h2179
                                          · linarith only [h2179, hlam, p2163_0]
                                          · rcases p2163_3 (m.d 2 5) (by simp) with h2181 | h2181
                                            · linarith only [h2149, h2181, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2163_1, u2elo1]
                                            · linarith only [h2160, h2181, hlam]
                                      · linarith only [h2148, h2176, hlam]
                                    · linarith only [h2175, hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    rcases p2163_3 (m.d 0 2) (by simp) with h2186 | h2186
                                    · rcases p2163_3 (m.d 1 2) (by simp) with h2187 | h2187
                                      · rcases p2163_3 (m.d 2 3) (by simp) with h2188 | h2188
                                        · linarith only [h2111, h2188, hlam]
                                        · rcases p2163_3 (m.d 2 4) (by simp) with h2190 | h2190
                                          · linarith only [h2112, h2190, hlam]
                                          · rcases p2163_3 (m.d 2 5) (by simp) with h2192 | h2192
                                            · linarith only [h2192, hlam, p2163_0]
                                            · rcases h4bigk with h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [hlam, p2194_0]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2133, h2162, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2194_1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2133, h2156, h2162, hc23, hc34, hlam, hphi, p2194_1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2113, hlam, p2194_0]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2133, hlam, p2194_0]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2109, hlam, p2194_1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [hlam, p2194_0]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h0, h2109, h2156, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2194_1, u2elo1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2150, hlam, p2194_1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2154, hlam, p2194_0]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2112, hlam, p2194_1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2148, hlam, p2194_1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [hlam, p2194_0]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2156, hlam, p2194_1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2160, hlam, p2194_0]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                rcases p2194_3 (m.d 0 4) (by simp) with h2210 | h2210
                                                · linarith only [h2113, h2210, hlam]
                                                · rcases p2194_3 (m.d 1 4) (by simp) with h2212 | h2212
                                                  · linarith only [h2150, h2212, hlam]
                                                  · rcases p2194_3 (m.d 2 4) (by simp) with h2214 | h2214
                                                    · linarith only [h2156, h2214, hlam]
                                                    · rcases p2194_3 (m.d 3 4) (by simp) with h2216 | h2216
                                                      · rcases p2194_3 (m.d 4 5) (by simp) with h2217 | h2217
                                                        · linarith only [h2162, h2217, hlam]
                                                        · linarith only [h2133, h2217, hlam]
                                                      · linarith only [h2113, h2216, hlam]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                rcases p2194_3 (m.d 0 4) (by simp) with h2221 | h2221
                                                · linarith only [h2113, h2221, hlam]
                                                · linarith only [h2109, h2221, hlam]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                rcases p2194_3 (m.d 0 4) (by simp) with h2224 | h2224
                                                · linarith only [h2113, h2224, hlam]
                                                · linarith only [h2112, h2224, hlam]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [hlam, p2194_0]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2112, h2133, h2156, hc23, hc34, hlam, hphi, p2194_1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2113, h2162, hc03, hc34, hlam, hphi, p2194_1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2148, h2156, h2162, hc23, hc34, hlam, hphi, p2194_1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2156, h2162, hc23, hc34, hlam, hphi, p2194_1]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [h2162, hlam, p2194_0]
                                              · have p2194_0 := h2194c.1
                                                have p2194_1 := h2194c.2.1
                                                have p2194_2 := h2194c.2.2.1
                                                have p2194_3 := h2194c.2.2.2
                                                linarith only [hlam, p2194_0]
                                      · linarith only [h2149, h2187, hlam]
                                    · linarith only [h2186, hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2163_1, u2elo1]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    rcases p2163_3 (m.d 0 2) (by simp) with h2238 | h2238
                                    · linarith only [h0, h2238, hlam]
                                    · linarith only [h2111, h2238, hlam]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    rcases p2163_3 (m.d 0 2) (by simp) with h2241 | h2241
                                    · linarith only [h0, h2241, hlam]
                                    · linarith only [h2112, h2241, hlam]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    rcases p2163_3 (m.d 0 2) (by simp) with h2244 | h2244
                                    · linarith only [h0, h2244, hlam]
                                    · linarith only [h0, h2110, h2149, h2244, hlam]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h2111, hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h2147, hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h2156, hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h2158, hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h2112, hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h2148, hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h0, h2110, h2148, h2154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2163_1, u2elo1]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h2160, hlam, p2163_1]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h0, h2110, h2149, hlam, p2163_1]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h2149, hlam, p2163_0]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h0, h2110, h2149, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2163_1, u2elo1]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [h0, h2110, h2149, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2163_1, u2elo1]
                                  · have p2163_0 := h2163c.1
                                    have p2163_1 := h2163c.2.1
                                    have p2163_2 := h2163c.2.2.1
                                    have p2163_3 := h2163c.2.2.2
                                    linarith only [hlam, p2163_0]
                                · rcases h2bigk with h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h0, hlam, p2262_1]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    rcases p2262_3 (m.d 0 2) (by simp) with h2265 | h2265
                                    · rcases p2262_3 (m.d 1 2) (by simp) with h2266 | h2266
                                      · rcases p2262_3 (m.d 2 3) (by simp) with h2267 | h2267
                                        · linarith only [h2267, hlam, p2262_0]
                                        · rcases p2262_3 (m.d 2 4) (by simp) with h2269 | h2269
                                          · linarith only [h2112, h2269, hlam]
                                          · linarith only [h2156, h2269, hlam]
                                      · linarith only [h2147, h2266, hlam]
                                    · linarith only [h2265, hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    rcases p2262_3 (m.d 0 2) (by simp) with h2274 | h2274
                                    · rcases p2262_3 (m.d 1 2) (by simp) with h2275 | h2275
                                      · rcases p2262_3 (m.d 2 3) (by simp) with h2276 | h2276
                                        · linarith only [h2111, h2276, hlam]
                                        · rcases p2262_3 (m.d 2 4) (by simp) with h2278 | h2278
                                          · linarith only [h2278, hlam, p2262_0]
                                          · rcases p2262_3 (m.d 2 5) (by simp) with h2280 | h2280
                                            · linarith only [h0, h2110, h2149, h2156, h2280, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2262_1, u2elo1]
                                            · linarith only [h2160, h2280, hlam]
                                      · linarith only [h2148, h2275, hlam]
                                    · linarith only [h2274, hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    rcases p2262_3 (m.d 0 2) (by simp) with h2285 | h2285
                                    · rcases p2262_3 (m.d 1 2) (by simp) with h2286 | h2286
                                      · rcases p2262_3 (m.d 2 3) (by simp) with h2287 | h2287
                                        · linarith only [h2111, h2287, hlam]
                                        · rcases p2262_3 (m.d 2 4) (by simp) with h2289 | h2289
                                          · linarith only [h2112, h2289, hlam]
                                          · rcases p2262_3 (m.d 2 5) (by simp) with h2291 | h2291
                                            · linarith only [h2291, hlam, p2262_0]
                                            · rcases h4bigk with h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c | h2293c
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [hlam, p2293_0]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h0, h2109, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2293_1, u2elo1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h0, h2109, h2156, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2293_1, u2elo1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2113, hlam, p2293_0]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2133, hlam, p2293_0]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2109, hlam, p2293_1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [hlam, p2293_0]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h0, h2109, h2156, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2293_1, u2elo1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2150, hlam, p2293_1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2154, hlam, p2293_0]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2112, hlam, p2293_1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2148, hlam, p2293_1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [hlam, p2293_0]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2156, hlam, p2293_1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2160, hlam, p2293_0]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2162, hc04, hc45, hlam, hphi, p2293_1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2148, h2156, h2162, hc23, hc45, hlam, hphi, ht34, p2293_1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2156, h2162, hc23, hc45, hlam, hphi, ht34, p2293_1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [hlam, p2293_0]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2162, hlam, p2293_0]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                rcases p2293_3 (m.d 0 4) (by simp) with h2314 | h2314
                                                · linarith only [h2314, hlam, p2293_0]
                                                · rcases p2293_3 (m.d 1 4) (by simp) with h2316 | h2316
                                                  · linarith only [h2154, h2316, hlam]
                                                  · rcases p2293_3 (m.d 2 4) (by simp) with h2318 | h2318
                                                    · linarith only [h2160, h2318, hlam]
                                                    · rcases p2293_3 (m.d 3 4) (by simp) with h2320 | h2320
                                                      · linarith only [h2162, h2320, hlam]
                                                      · linarith only [h2113, h2320, hlam]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                rcases p2293_3 (m.d 0 4) (by simp) with h2323 | h2323
                                                · linarith only [h2133, h2323, hlam]
                                                · linarith only [h2109, h2323, hlam]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                rcases p2293_3 (m.d 0 4) (by simp) with h2326 | h2326
                                                · linarith only [h2133, h2326, hlam]
                                                · linarith only [h2112, h2326, hlam]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [h2108, h2113, h2147, hc23, hc45, hlam, hphi, ht34, p2293_1]
                                              · have p2293_0 := h2293c.1
                                                have p2293_1 := h2293c.2.1
                                                have p2293_2 := h2293c.2.2.1
                                                have p2293_3 := h2293c.2.2.2
                                                linarith only [hlam, p2293_0]
                                      · linarith only [h2149, h2286, hlam]
                                    · linarith only [h2285, hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2262_1, u2elo1]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    rcases p2262_3 (m.d 0 2) (by simp) with h2335 | h2335
                                    · linarith only [h0, h2335, hlam]
                                    · linarith only [h2111, h2335, hlam]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    rcases p2262_3 (m.d 0 2) (by simp) with h2338 | h2338
                                    · linarith only [h0, h2338, hlam]
                                    · linarith only [h2112, h2338, hlam]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    rcases p2262_3 (m.d 0 2) (by simp) with h2341 | h2341
                                    · linarith only [h0, h2341, hlam]
                                    · linarith only [h0, h2341, hc01, hlam, hphi, ht12, p2262_1, u2elo1]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h2111, hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h2147, hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h2156, hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h2158, hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h2112, hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h2148, hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h0, h2109, h2148, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2262_1, u2elo0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h2160, hlam, p2262_1]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2262_1, u2elo4]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h2149, hlam, p2262_0]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h0, h2110, h2149, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2262_1, u2elo1]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [h0, h2110, h2149, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2262_1, u2elo1]
                                  · have p2262_0 := h2262c.1
                                    have p2262_1 := h2262c.2.1
                                    have p2262_2 := h2262c.2.2.1
                                    have p2262_3 := h2262c.2.2.2
                                    linarith only [hlam, p2262_0]
                  · linarith only [h0, h2149, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2108, h2147, h2148, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2147, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h0, h2109, h2112, hlam]
      · linarith only [h0, h2108, h2111, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2364 | h2364
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2365 | h2365
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2366 | h2366
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2367 | h2367
            · linarith only [h2108, h2110, h2366, h2367, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2369 | h2369
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2370 | h2370
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2371 | h2371
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2372 | h2372
                    · linarith only [h2108, h2110, h2371, h2372, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h2108, h2110, h2366, h2369, h2371, h2372, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2109, h2370, h2371, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h0, h2108, h2369, h2370, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2108, h2369, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2378 | h2378
            · linarith only [h2109, h2110, h2378, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2380 | h2380
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2381 | h2381
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2382 | h2382
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2383 | h2383
                    · linarith only [h2108, h2110, h2366, h2383, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2385 | h2385
                      · linarith only [h2108, h2110, h2382, h2385, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2387 | h2387
                        · linarith only [h2109, h2110, h2382, h2387, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2389 | h2389
                          · linarith only [h0, h2364, h2366, h2389, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2391 | h2391
                            · linarith only [h2110, h2385, h2391, hc01, hlam, hphi, ht12, u2elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2393 | h2393
                              · linarith only [h2109, h2110, h2381, h2387, h2393, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2395 | h2395
                                · linarith only [h2109, h2110, h2380, h2383, h2387, h2395, hc23, hc34, hlam, hphi]
                                · rcases h2bigk with h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h0, hlam, p2397_1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    rcases p2397_3 (m.d 0 2) (by simp) with h2400 | h2400
                                    · rcases p2397_3 (m.d 1 2) (by simp) with h2401 | h2401
                                      · rcases p2397_3 (m.d 2 3) (by simp) with h2402 | h2402
                                        · linarith only [h2402, hlam, p2397_0]
                                        · rcases p2397_3 (m.d 2 4) (by simp) with h2404 | h2404
                                          · linarith only [h2365, h2404, hlam]
                                          · linarith only [h2389, h2404, hlam]
                                      · linarith only [h2380, h2401, hlam]
                                    · linarith only [h2400, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    rcases p2397_3 (m.d 0 2) (by simp) with h2409 | h2409
                                    · rcases p2397_3 (m.d 1 2) (by simp) with h2410 | h2410
                                      · rcases p2397_3 (m.d 2 3) (by simp) with h2411 | h2411
                                        · linarith only [h2364, h2411, hlam]
                                        · rcases p2397_3 (m.d 2 4) (by simp) with h2413 | h2413
                                          · linarith only [h2413, hlam, p2397_0]
                                          · rcases p2397_3 (m.d 2 5) (by simp) with h2415 | h2415
                                            · linarith only [h2382, h2415, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2397_1, u2elo1]
                                            · linarith only [h2393, h2415, hlam]
                                      · linarith only [h2381, h2410, hlam]
                                    · linarith only [h2409, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    rcases p2397_3 (m.d 0 2) (by simp) with h2420 | h2420
                                    · rcases p2397_3 (m.d 1 2) (by simp) with h2421 | h2421
                                      · rcases p2397_3 (m.d 2 3) (by simp) with h2422 | h2422
                                        · linarith only [h2364, h2422, hlam]
                                        · rcases p2397_3 (m.d 2 4) (by simp) with h2424 | h2424
                                          · linarith only [h2365, h2424, hlam]
                                          · rcases p2397_3 (m.d 2 5) (by simp) with h2426 | h2426
                                            · linarith only [h2426, hlam, p2397_0]
                                            · rcases h4bigk with h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [hlam, p2428_0]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2109, h2110, h2380, h2383, h2385, hc23, hc35, hlam, hphi, p2428_1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h0, h2109, h2389, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2428_1, u2elo1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2366, hlam, p2428_0]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2378, hlam, p2428_0]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2109, hlam, p2428_1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [hlam, p2428_0]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h0, h2109, h2389, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2428_1, u2elo1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2383, hlam, p2428_1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2387, hlam, p2428_0]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2365, hlam, p2428_1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2381, hlam, p2428_1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [hlam, p2428_0]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2389, hlam, p2428_1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2393, hlam, p2428_0]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2395, hc04, hc45, hlam, hphi, p2428_1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2395, hc14, hc45, hlam, hphi, p2428_1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2389, h2395, hc23, hc45, hlam, hphi, ht34, p2428_1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [hlam, p2428_0]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2395, hlam, p2428_0]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                rcases p2428_3 (m.d 0 4) (by simp) with h2449 | h2449
                                                · linarith only [h2449, hlam, p2428_0]
                                                · rcases p2428_3 (m.d 1 4) (by simp) with h2451 | h2451
                                                  · linarith only [h2387, h2451, hlam]
                                                  · rcases p2428_3 (m.d 2 4) (by simp) with h2453 | h2453
                                                    · linarith only [h2393, h2453, hlam]
                                                    · rcases p2428_3 (m.d 3 4) (by simp) with h2455 | h2455
                                                      · linarith only [h2395, h2455, hlam]
                                                      · linarith only [h2366, h2455, hlam]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                rcases p2428_3 (m.d 0 4) (by simp) with h2458 | h2458
                                                · linarith only [h2378, h2458, hlam]
                                                · linarith only [h2109, h2458, hlam]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                rcases p2428_3 (m.d 0 4) (by simp) with h2461 | h2461
                                                · linarith only [h2378, h2461, hlam]
                                                · linarith only [h2365, h2461, hlam]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [h2108, h2366, h2380, hc23, hc45, hlam, hphi, ht34, p2428_1]
                                              · have p2428_0 := h2428c.1
                                                have p2428_1 := h2428c.2.1
                                                have p2428_2 := h2428c.2.2.1
                                                have p2428_3 := h2428c.2.2.2
                                                linarith only [hlam, p2428_0]
                                      · linarith only [h2382, h2421, hlam]
                                    · linarith only [h2420, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2397_1, u2elo1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    rcases p2397_3 (m.d 0 2) (by simp) with h2470 | h2470
                                    · linarith only [h0, h2470, hlam]
                                    · linarith only [h2364, h2470, hlam]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    rcases p2397_3 (m.d 0 2) (by simp) with h2473 | h2473
                                    · linarith only [h0, h2473, hlam]
                                    · linarith only [h2365, h2473, hlam]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    rcases p2397_3 (m.d 0 2) (by simp) with h2476 | h2476
                                    · linarith only [h0, h2476, hlam]
                                    · linarith only [h0, h2476, hc01, hlam, hphi, ht12, p2397_1, u2elo1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2364, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2380, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2389, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2391, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2365, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2381, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h0, h2109, h2381, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2397_1, u2elo0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2393, hlam, p2397_1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2397_1, u2elo4]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2382, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2382, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2397_1, u2elo1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2382, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2397_1, u2elo1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hlam, p2397_0]
                  · linarith only [h0, h2382, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2108, h2380, h2381, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2108, h2380, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h2109, h2365, hlam]
      · linarith only [h0, h2108, h2364, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2499 | h2499
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2500 | h2500
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2501 | h2501
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2502 | h2502
          · linarith only [h2108, h2109, h2502, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2504 | h2504
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2505 | h2505
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2506 | h2506
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2507 | h2507
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2508 | h2508
                    · linarith only [h2108, h2109, h2502, h2508, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2510 | h2510
                      · linarith only [h2108, h2109, h2506, h2510, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2512 | h2512
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2513 | h2513
                          · linarith only [h2109, h2508, h2513, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2515 | h2515
                            · linarith only [h2505, h2510, h2515, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2517 | h2517
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2518 | h2518
                                · rcases h2bigk with h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h0, hlam, p2519_1]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    rcases p2519_3 (m.d 0 2) (by simp) with h2522 | h2522
                                    · rcases p2519_3 (m.d 1 2) (by simp) with h2523 | h2523
                                      · rcases p2519_3 (m.d 2 3) (by simp) with h2524 | h2524
                                        · linarith only [h2524, hlam, p2519_0]
                                        · rcases p2519_3 (m.d 2 4) (by simp) with h2526 | h2526
                                          · linarith only [h2501, h2526, hlam]
                                          · linarith only [h2513, h2526, hlam]
                                      · linarith only [h2505, h2523, hlam]
                                    · linarith only [h2522, hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2517, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2519_1, u2elo0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    rcases p2519_3 (m.d 0 2) (by simp) with h2532 | h2532
                                    · rcases p2519_3 (m.d 1 2) (by simp) with h2533 | h2533
                                      · rcases p2519_3 (m.d 2 3) (by simp) with h2534 | h2534
                                        · linarith only [h2500, h2534, hlam]
                                        · rcases p2519_3 (m.d 2 4) (by simp) with h2536 | h2536
                                          · linarith only [h2501, h2536, hlam]
                                          · linarith only [h2517, h2536, hlam]
                                      · linarith only [h2507, h2533, hlam]
                                    · linarith only [h2532, hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2519_1, u2elo1]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    rcases p2519_3 (m.d 0 2) (by simp) with h2543 | h2543
                                    · linarith only [h0, h2543, hlam]
                                    · linarith only [h2500, h2543, hlam]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2517, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2519_1, u2elo1]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    rcases p2519_3 (m.d 0 2) (by simp) with h2547 | h2547
                                    · linarith only [h0, h2547, hlam]
                                    · linarith only [h2109, h2499, h2501, h2506, h2507, h2517, h2547, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2500, hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2505, hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2513, hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2515, hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2501, hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2506, hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2501, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2519_1, u2elo0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h0, h2501, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2519_1, u2elo1]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2519_1, u2elo4]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2507, hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2109, h2499, h2506, h2507, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2519_1, u2elo1]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [h2517, hlam, p2519_0]
                                  · have p2519_0 := h2519c.1
                                    have p2519_1 := h2519c.2.1
                                    have p2519_2 := h2519c.2.2.1
                                    have p2519_3 := h2519c.2.2.2
                                    linarith only [hlam, p2519_0]
                                · linarith only [h2109, h2501, h2508, h2517, h2518, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · linarith only [h2109, h2499, h2506, h2512, h2517, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h2109, h2499, h2505, h2510, h2512, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h2109, h2506, h2507, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2108, h2505, h2506, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2505, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h2109, h2499, h2504, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2572 | h2572
          · linarith only [h0, h2108, h2501, h2572, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2574 | h2574
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2575 | h2575
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2576 | h2576
                · linarith only [h0, h2501, h2576, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2108, h2575, h2576, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2575, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h0, h2499, h2501, h2574, hlam]
      · linarith only [h0, h2108, h2500, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2582 | h2582
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2583 | h2583
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2584 | h2584
          · linarith only [h2108, h2109, h2584, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2586 | h2586
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2587 | h2587
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2588 | h2588
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2589 | h2589
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2590 | h2590
                    · linarith only [h2108, h2109, h2584, h2588, h2590, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2592 | h2592
                      · linarith only [h2108, h2109, h2588, h2592, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2594 | h2594
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2595 | h2595
                          · linarith only [h2108, h2499, h2587, h2590, h2594, h2595, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2597 | h2597
                            · linarith only [h2108, h2499, h2587, h2592, h2597, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2599 | h2599
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2600 | h2600
                                · rcases h2bigk with h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h0, hlam, p2601_1]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    rcases p2601_3 (m.d 0 2) (by simp) with h2604 | h2604
                                    · rcases p2601_3 (m.d 1 2) (by simp) with h2605 | h2605
                                      · rcases p2601_3 (m.d 2 3) (by simp) with h2606 | h2606
                                        · linarith only [h2606, hlam, p2601_0]
                                        · rcases p2601_3 (m.d 2 4) (by simp) with h2608 | h2608
                                          · linarith only [h2583, h2608, hlam]
                                          · linarith only [h2595, h2608, hlam]
                                      · linarith only [h2587, h2605, hlam]
                                    · linarith only [h2604, hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h0, h2599, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2601_1, u2elo1]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    rcases p2601_3 (m.d 0 2) (by simp) with h2614 | h2614
                                    · rcases p2601_3 (m.d 1 2) (by simp) with h2615 | h2615
                                      · rcases p2601_3 (m.d 2 3) (by simp) with h2616 | h2616
                                        · linarith only [h2582, h2616, hlam]
                                        · rcases p2601_3 (m.d 2 4) (by simp) with h2618 | h2618
                                          · linarith only [h2583, h2618, hlam]
                                          · linarith only [h2599, h2618, hlam]
                                      · linarith only [h2589, h2615, hlam]
                                    · linarith only [h2614, hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2601_1, u2elo1]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    rcases p2601_3 (m.d 0 2) (by simp) with h2625 | h2625
                                    · linarith only [h0, h2625, hlam]
                                    · linarith only [h2582, h2625, hlam]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2599, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2601_1, u2elo1]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    rcases p2601_3 (m.d 0 2) (by simp) with h2629 | h2629
                                    · linarith only [h0, h2629, hlam]
                                    · linarith only [h2583, h2599, h2629, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2601_1, u2elo1]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2582, hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2587, hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2595, hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2597, hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2583, hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2588, hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2583, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2601_1, u2elo0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2583, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2601_1, u2elo0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2601_1, u2elo4]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2589, hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2589, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2601_1, u2elo1]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [h2599, hlam, p2601_0]
                                  · have p2601_0 := h2601c.1
                                    have p2601_1 := h2601c.2.1
                                    have p2601_2 := h2601c.2.2.1
                                    have p2601_3 := h2601c.2.2.2
                                    linarith only [hlam, p2601_0]
                                · linarith only [h2499, h2583, h2590, h2594, h2599, h2600, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2648 | h2648
                                · rcases h2bigk with h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c | h2649c
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h0, hlam, p2649_1]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    rcases p2649_3 (m.d 0 2) (by simp) with h2652 | h2652
                                    · rcases p2649_3 (m.d 1 2) (by simp) with h2653 | h2653
                                      · rcases p2649_3 (m.d 2 3) (by simp) with h2654 | h2654
                                        · linarith only [h2654, hlam, p2649_0]
                                        · rcases p2649_3 (m.d 2 4) (by simp) with h2656 | h2656
                                          · linarith only [h2583, h2656, hlam]
                                          · linarith only [h2595, h2656, hlam]
                                      · linarith only [h2587, h2653, hlam]
                                    · linarith only [h2652, hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    rcases p2649_3 (m.d 0 2) (by simp) with h2661 | h2661
                                    · rcases p2649_3 (m.d 1 2) (by simp) with h2662 | h2662
                                      · rcases p2649_3 (m.d 2 3) (by simp) with h2663 | h2663
                                        · linarith only [h2582, h2663, hlam]
                                        · rcases p2649_3 (m.d 2 4) (by simp) with h2665 | h2665
                                          · linarith only [h2665, hlam, p2649_0]
                                          · rcases p2649_3 (m.d 2 5) (by simp) with h2667 | h2667
                                            · linarith only [h2109, h2586, h2588, h2595, h2599, h2667, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2649_1, u2elo1]
                                            · linarith only [h2599, h2667, hlam]
                                      · linarith only [h2588, h2662, hlam]
                                    · linarith only [h2661, hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    rcases p2649_3 (m.d 0 2) (by simp) with h2672 | h2672
                                    · rcases p2649_3 (m.d 1 2) (by simp) with h2673 | h2673
                                      · rcases p2649_3 (m.d 2 3) (by simp) with h2674 | h2674
                                        · linarith only [h2582, h2674, hlam]
                                        · rcases p2649_3 (m.d 2 4) (by simp) with h2676 | h2676
                                          · linarith only [h2583, h2676, hlam]
                                          · rcases p2649_3 (m.d 2 5) (by simp) with h2678 | h2678
                                            · linarith only [h2678, hlam, p2649_0]
                                            · rcases h4bigk with h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [hlam, p2680_0]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2109, hlam, p2680_0]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                rcases p2680_3 (m.d 0 4) (by simp) with h2683 | h2683
                                                · rcases p2680_3 (m.d 1 4) (by simp) with h2684 | h2684
                                                  · rcases p2680_3 (m.d 2 4) (by simp) with h2685 | h2685
                                                    · linarith only [h2583, h2685, hlam]
                                                    · rcases p2680_3 (m.d 3 4) (by simp) with h2687 | h2687
                                                      · rcases p2680_3 (m.d 4 5) (by simp) with h2688 | h2688
                                                        · linarith only [h2586, h2688, hlam]
                                                        · linarith only [h2599, h2688, hlam]
                                                      · linarith only [h2595, h2687, hlam]
                                                  · linarith only [h2588, h2684, hlam]
                                                · linarith only [h2583, h2683, hlam]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2584, hlam, p2680_0]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2583, h2595, h2599, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2680_1, u2elo0]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2109, h2588, hc01, hlam, hphi, ht12, p2680_1, u2elo1]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [hlam, p2680_0]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                rcases p2680_3 (m.d 0 4) (by simp) with h2698 | h2698
                                                · linarith only [h2109, h2698, hlam]
                                                · linarith only [h2583, h2698, hlam]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2590, hlam, p2680_1]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2588, h2595, h2599, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2680_1, u2elo1]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2583, hlam, p2680_1]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2588, hlam, p2680_1]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [hlam, p2680_0]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2595, hlam, p2680_1]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2599, hlam, p2680_0]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2586, h2595, h2599, hc23, hc34, hlam, hphi, p2680_1]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2108, h2109, h2587, hc23, hc34, hlam, hphi, p2680_1]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                rcases p2680_3 (m.d 0 4) (by simp) with h2710 | h2710
                                                · linarith only [h2584, h2710, hlam]
                                                · linarith only [h2583, h2710, hlam]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [hlam, p2680_0]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2595, h2599, hc23, hc34, hlam, hphi, p2680_1]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2586, hlam, p2680_0]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2594, hlam, p2680_0]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h0, h2583, h2586, h2595, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2680_1, u2elo1]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [h2648, hlam, p2680_0]
                                              · have p2680_0 := h2680c.1
                                                have p2680_1 := h2680c.2.1
                                                have p2680_2 := h2680c.2.2.1
                                                have p2680_3 := h2680c.2.2.2
                                                linarith only [hlam, p2680_0]
                                      · linarith only [h2589, h2673, hlam]
                                    · linarith only [h2672, hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2649_1, u2elo1]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    rcases p2649_3 (m.d 0 2) (by simp) with h2724 | h2724
                                    · linarith only [h0, h2724, hlam]
                                    · linarith only [h2582, h2724, hlam]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    rcases p2649_3 (m.d 0 2) (by simp) with h2727 | h2727
                                    · linarith only [h0, h2727, hlam]
                                    · linarith only [h2583, h2727, hlam]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    rcases p2649_3 (m.d 0 2) (by simp) with h2730 | h2730
                                    · linarith only [h0, h2730, hlam]
                                    · linarith only [h2730, hc02, hlam, hphi, p2649_1, u2elo1]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h2582, hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h2587, hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h2595, hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h2597, hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h2583, hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h2588, hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h2583, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2649_1, u2elo0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h2599, hlam, p2649_1]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2649_1, u2elo4]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h2589, hlam, p2649_0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h2589, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2649_1, u2elo1]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [h2583, h2586, h2595, h2599, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2649_1, u2elo0]
                                  · have p2649_0 := h2649c.1
                                    have p2649_1 := h2649c.2.1
                                    have p2649_2 := h2649c.2.2.1
                                    have p2649_3 := h2649c.2.2.2
                                    linarith only [hlam, p2649_0]
                                · linarith only [h0, h2108, h2583, h2584, h2586, h2587, h2648, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h2109, h2586, h2594, hlam]
                  · linarith only [h0, h2108, h2587, h2589, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h2108, h2587, h2588, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2587, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2753 | h2753
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2754 | h2754
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2755 | h2755
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2756 | h2756
                    · linarith only [h2108, h2109, h2754, h2756, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2758 | h2758
                      · linarith only [h2108, h2109, h2754, h2758, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2760 | h2760
                        · linarith only [h2108, h2109, h2586, h2753, h2754, h2760, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h2108, h2109, h2753, h2760, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2108, h2753, h2755, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h2583, h2754, hlam]
              · linarith only [h0, h2108, h2753, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2766 | h2766
          · linarith only [h0, h2108, h2583, h2766, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2768 | h2768
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2769 | h2769
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2770 | h2770
                · linarith only [h0, h2583, h2770, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2108, h2769, h2770, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2769, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2774 | h2774
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2775 | h2775
                · linarith only [h0, h2108, h2583, h2774, h2775, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h2108, h2774, h2775, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2108, h2774, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h2108, h2582, hlam]

end R2N4
