import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x1_x1_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1845 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2109 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2111 | h2111
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2112 | h2112
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2113 | h2113
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2114 | h2114
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2115 | h2115
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2116 | h2116
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2117 | h2117
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2118 | h2118
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2119 | h2119
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2120 | h2120
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2121 | h2121
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2122 | h2122
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2123 | h2123
                          · rcases h3bigk with h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c | h2124c
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h1845, hlam, p2124_1]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h2120, h2123, hc03, hc45, hlam, hphi, ht0b, ht5b, p2124_1]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              rcases p2124_3 (m.d 0 3) (by simp) with h2128 | h2128
                              · rcases p2124_3 (m.d 1 3) (by simp) with h2129 | h2129
                                · rcases p2124_3 (m.d 2 3) (by simp) with h2130 | h2130
                                  · linarith only [h2110, h2130, hlam]
                                  · linarith only [h2120, h2130, hlam]
                                · linarith only [h2117, h2129, hlam]
                              · linarith only [h2128, hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              rcases p2124_3 (m.d 0 3) (by simp) with h2135 | h2135
                              · rcases p2124_3 (m.d 1 3) (by simp) with h2136 | h2136
                                · rcases p2124_3 (m.d 2 3) (by simp) with h2137 | h2137
                                  · linarith only [h2110, h2137, hlam]
                                  · linarith only [h2121, h2137, hlam]
                                · linarith only [h2118, h2136, hlam]
                              · linarith only [h2135, hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h1845, h2109, h2115, h2116, h2120, h2123, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2124_1]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h2115, h2120, h2123, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2124_1]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              rcases p2124_3 (m.d 0 3) (by simp) with h2145 | h2145
                              · linarith only [h1845, h2145, hlam]
                              · linarith only [h2112, h2145, hlam]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              rcases p2124_3 (m.d 0 3) (by simp) with h2148 | h2148
                              · linarith only [h1845, h2148, hlam]
                              · linarith only [h2113, h2148, hlam]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h2110, hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h2115, hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h0, h2110, h2123, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2124_1]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              rcases p2124_3 (m.d 0 3) (by simp) with h2155 | h2155
                              · rcases p2124_3 (m.d 1 3) (by simp) with h2156 | h2156
                                · rcases p2124_3 (m.d 2 3) (by simp) with h2157 | h2157
                                  · rcases p2124_3 (m.d 3 4) (by simp) with h2158 | h2158
                                    · linarith only [h2120, h2158, hlam]
                                    · linarith only [h2123, h2158, hlam]
                                  · linarith only [h2157, hlam, p2124_0]
                                · linarith only [h2118, h2156, hlam]
                              · linarith only [h2113, h2155, hlam]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h2112, hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h2117, hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h2120, hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h0, h2109, h2116, h2120, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2124_1]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h2113, hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h2118, hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h2121, hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [h2123, hlam, p2124_0]
                            · have p2124_0 := h2124c.1
                              have p2124_1 := h2124c.2.1
                              have p2124_2 := h2124c.2.2.1
                              have p2124_3 := h2124c.2.2.2
                              linarith only [hlam, p2124_0]
                          · linarith only [h1845, h2109, h2115, h2116, h2122, h2123, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h2114, h2122, hc24, hlam, hphi, u4elo0]
                      · linarith only [h1845, h2109, h2115, h2118, h2119, h2120, h2121, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2177 | h2177
                      · linarith only [h1845, h2109, h2115, h2117, h2120, h2177, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2179 | h2179
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2180 | h2180
                          · rcases h3bigk with h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h1845, hlam, p2181_1]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              rcases p2181_3 (m.d 0 3) (by simp) with h2184 | h2184
                              · rcases p2181_3 (m.d 1 3) (by simp) with h2185 | h2185
                                · rcases p2181_3 (m.d 2 3) (by simp) with h2186 | h2186
                                  · linarith only [h2110, h2186, hlam]
                                  · rcases p2181_3 (m.d 3 4) (by simp) with h2188 | h2188
                                    · linarith only [h2112, h2188, hlam]
                                    · linarith only [h2120, h2188, hlam]
                                · linarith only [h2115, h2185, hlam]
                              · linarith only [h2110, h2184, hlam]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              rcases p2181_3 (m.d 0 3) (by simp) with h2193 | h2193
                              · rcases p2181_3 (m.d 1 3) (by simp) with h2194 | h2194
                                · rcases p2181_3 (m.d 2 3) (by simp) with h2195 | h2195
                                  · linarith only [h2110, h2195, hlam]
                                  · rcases p2181_3 (m.d 3 4) (by simp) with h2197 | h2197
                                    · linarith only [h2197, hlam, p2181_0]
                                    · rcases p2181_3 (m.d 3 5) (by simp) with h2199 | h2199
                                      · linarith only [h2113, h2199, hlam]
                                      · rcases h3emin with h2201 | h2201 | h2201 | h2201 | h2201
                                        · rcases h4bigk with h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c | h2202c
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [hlam, p2202_0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [hc14, hlam, hphi, p2202_1, u4elo0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h1845, h2109, h2115, h2118, h2119, h2177, h2179, hc12, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p2202_1, u4elo0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2202_1, u4elo0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            rcases p2202_3 (m.d 0 4) (by simp) with h2207 | h2207
                                            · rcases p2202_3 (m.d 1 4) (by simp) with h2208 | h2208
                                              · linarith only [h2109, h2208, hlam]
                                              · linarith only [h2119, h2208, hlam]
                                            · linarith only [h2207, hlam, p2202_0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h2109, hlam, p2202_1]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [hlam, p2202_0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h1845, h2109, h2115, h2179, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2202_1]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h1845, h2109, h2115, h2177, h2180, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2202_1]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h1845, h2109, h2115, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2202_1]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h2111, hlam, p2202_1]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h2116, hlam, p2202_1]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [hlam, p2202_0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h2120, hlam, p2202_1]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h1845, h2109, h2115, h2116, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2202_1]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h2112, hlam, p2202_1]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h2117, hlam, p2202_0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p2181_1, p2202_1]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [hlam, p2202_0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h1845, h2115, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2181_1, p2202_1]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h2114, hlam, p2202_0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h2119, hlam, p2202_0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h2179, hlam, p2202_0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [h2180, hlam, p2202_0]
                                          · have p2202_0 := h2202c.1
                                            have p2202_1 := h2202c.2.1
                                            have p2202_2 := h2202c.2.2.1
                                            have p2202_3 := h2202c.2.2.2
                                            linarith only [hlam, p2202_0]
                                        · rcases h4bigk with h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [hlam, p2232_0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [hc14, hlam, hphi, p2232_1, u4elo0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h2179, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2232_1, u4elo0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2232_1, u4elo0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            rcases p2232_3 (m.d 0 4) (by simp) with h2237 | h2237
                                            · rcases p2232_3 (m.d 1 4) (by simp) with h2238 | h2238
                                              · linarith only [h2109, h2238, hlam]
                                              · linarith only [h2119, h2238, hlam]
                                            · linarith only [h2237, hlam, p2232_0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h2109, hlam, p2232_1]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [hlam, p2232_0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h1845, h2109, h2115, h2179, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2232_1]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h1845, h2109, h2115, h2177, h2180, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2232_1]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h1845, h2109, h2115, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2232_1]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h2111, hlam, p2232_1]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h2116, hlam, p2232_1]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [hlam, p2232_0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h2120, hlam, p2232_1]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h1845, h2109, h2115, h2116, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2232_1]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h2112, hlam, p2232_1]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h2117, hlam, p2232_0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [hc24, hlam, hphi, p2232_1, u4elo3]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [hlam, p2232_0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h1845, h2115, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2181_1, p2232_1]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h2114, hlam, p2232_0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h2119, hlam, p2232_0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h2179, hlam, p2232_0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [h2180, hlam, p2232_0]
                                          · have p2232_0 := h2232c.1
                                            have p2232_1 := h2232c.2.1
                                            have p2232_2 := h2232c.2.2.1
                                            have p2232_3 := h2232c.2.2.2
                                            linarith only [hlam, p2232_0]
                                        · linarith only [h2177, h2201, hc35, hlam]
                                        · linarith only [h1845, h2115, h2201, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2181_1]
                                        · linarith only [h2113, h2114, h2201, hlam, ht34, u4elo0]
                                · linarith only [h2117, h2194, hlam]
                              · linarith only [h2193, hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              rcases p2181_3 (m.d 0 3) (by simp) with h2267 | h2267
                              · rcases p2181_3 (m.d 1 3) (by simp) with h2268 | h2268
                                · rcases p2181_3 (m.d 2 3) (by simp) with h2269 | h2269
                                  · linarith only [h2110, h2269, hlam]
                                  · rcases p2181_3 (m.d 3 4) (by simp) with h2271 | h2271
                                    · linarith only [h2112, h2271, hlam]
                                    · linarith only [h2180, h2271, hlam]
                                · linarith only [h2118, h2268, hlam]
                              · linarith only [h2267, hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h1845, h2109, h2115, h2118, h2119, h2177, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2181_1]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h1845, h2109, h2118, h2119, h2177, hlam, p2181_2]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              rcases p2181_3 (m.d 0 3) (by simp) with h2279 | h2279
                              · linarith only [h1845, h2279, hlam]
                              · linarith only [h2112, h2279, hlam]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              rcases p2181_3 (m.d 0 3) (by simp) with h2282 | h2282
                              · linarith only [h1845, h2282, hlam]
                              · linarith only [h2113, h2282, hlam]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h2110, hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h2115, hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h2120, hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h2177, hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h2112, hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h2117, hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, p2181_1, u4elo3]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h2109, h2117, h2177, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2181_1]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h2113, hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h2118, hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h2113, h2114, hc23, hlam, hphi, ht34, p2181_1, u4elo0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [h2180, hlam, p2181_0]
                            · have p2181_0 := h2181c.1
                              have p2181_1 := h2181c.2.1
                              have p2181_2 := h2181c.2.2.1
                              have p2181_3 := h2181c.2.2.2
                              linarith only [hlam, p2181_0]
                          · linarith only [h2179, h2180, hc34, hlam, hphi, u4elo2]
                        · linarith only [h1845, h2109, h2115, h2119, h2179, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h2114, h2119, hc14, hlam, hphi, u4elo0]
                · linarith only [h0, h1845, h2110, h2113, h2118, hc01, hc12, hlam, hphi]
              · linarith only [h1845, h2109, h2116, h2117, hc24, hlam, hphi, u4elo3]
            · linarith only [h0, h2109, h2116, hc14, hlam, hphi, u4elo2]
          · linarith only [h0, h2110, h2115, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2307 | h2307
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2308 | h2308
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2309 | h2309
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2310 | h2310
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2311 | h2311
                  · linarith only [h1845, h2109, h2114, h2311, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2313 | h2313
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2314 | h2314
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2315 | h2315
                        · linarith only [h2109, h2114, h2308, h2315, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2317 | h2317
                          · linarith only [h2109, h2114, h2308, h2313, h2317, hlam]
                          · rcases h3bigk with h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [h1845, hlam, p2319_1]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              rcases p2319_3 (m.d 0 3) (by simp) with h2322 | h2322
                              · rcases p2319_3 (m.d 1 3) (by simp) with h2323 | h2323
                                · rcases p2319_3 (m.d 2 3) (by simp) with h2324 | h2324
                                  · linarith only [h2110, h2324, hlam]
                                  · rcases p2319_3 (m.d 3 4) (by simp) with h2326 | h2326
                                    · linarith only [h2112, h2326, hlam]
                                    · rcases p2319_3 (m.d 3 5) (by simp) with h2328 | h2328
                                      · linarith only [h2113, h2328, hlam]
                                      · rcases h3emin with h2330 | h2330 | h2330 | h2330 | h2330
                                        · rcases h4bigk with h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c | h2331c
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [hlam, p2331_0]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2114, hc14, hlam, hphi, p2331_1, u4elo4]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2114, hc24, hlam, hphi, p2331_1, u4elo4]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2114, hc34, hlam, hphi, p2331_1, u4elo4]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2114, hlam, p2331_0]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2109, hlam, p2331_1]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [hlam, p2331_0]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [hc24, hlam, hphi, p2331_1, u4elo1]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2109, h2114, hc34, hlam, hphi, p2331_1, u4elo4]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2311, hlam, p2331_0]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2111, hlam, p2331_1]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2308, hlam, p2331_1]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [hlam, p2331_0]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2331_1, u4elo2]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2315, hlam, p2331_0]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2112, hlam, p2331_1]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2309, hlam, p2331_0]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2313, hlam, p2331_0]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [hlam, p2331_0]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2317, hlam, p2331_0]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2331_1, u4elo4]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [hc14, hlam, hphi, p2331_1, u4elo4]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2331_1, u4elo4]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2331_1, u4elo4]
                                          · have p2331_0 := h2331c.1
                                            have p2331_1 := h2331c.2.1
                                            have p2331_2 := h2331c.2.2.1
                                            have p2331_3 := h2331c.2.2.2
                                            linarith only [hlam, p2331_0]
                                        · rcases h4bigk with h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c | h2357c
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [hlam, p2357_0]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2114, h2308, h2313, hc34, hlam, hphi, p2357_1, u4elo4]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2114, h2313, hc34, hlam, hphi, p2357_1, u4elo4]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2114, hc34, hlam, hphi, p2357_1, u4elo4]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2114, hlam, p2357_0]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2109, hlam, p2357_1]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [hlam, p2357_0]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2357_1, u4elo1]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2109, h2114, hc34, hlam, hphi, p2357_1, u4elo4]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2311, hlam, p2357_0]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2111, hlam, p2357_1]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2308, hlam, p2357_1]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [hlam, p2357_0]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2357_1, u4elo2]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2315, hlam, p2357_0]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2112, hlam, p2357_1]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2309, hlam, p2357_0]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2313, hlam, p2357_0]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [hlam, p2357_0]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2317, hlam, p2357_0]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2357_1, u4elo4]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2308, hc24, hlam, hphi, p2357_1, u4elo4]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2357_1, u4elo4]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2357_1, u4elo4]
                                          · have p2357_0 := h2357c.1
                                            have p2357_1 := h2357c.2.1
                                            have p2357_2 := h2357c.2.2.1
                                            have p2357_3 := h2357c.2.2.2
                                            linarith only [hlam, p2357_0]
                                        · linarith only [h0, h2110, h2330, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2319_1]
                                        · linarith only [h0, h2110, h2314, h2317, h2330, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2319_1]
                                        · linarith only [h0, h2110, h2314, h2330, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2319_1]
                                · linarith only [h2307, h2323, hlam]
                              · linarith only [h2110, h2322, hlam]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              rcases p2319_3 (m.d 0 3) (by simp) with h2388 | h2388
                              · rcases p2319_3 (m.d 1 3) (by simp) with h2389 | h2389
                                · rcases p2319_3 (m.d 2 3) (by simp) with h2390 | h2390
                                  · linarith only [h2110, h2390, hlam]
                                  · linarith only [h2313, h2390, hlam]
                                · linarith only [h2309, h2389, hlam]
                              · linarith only [h2388, hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              rcases p2319_3 (m.d 0 3) (by simp) with h2395 | h2395
                              · rcases p2319_3 (m.d 1 3) (by simp) with h2396 | h2396
                                · rcases p2319_3 (m.d 2 3) (by simp) with h2397 | h2397
                                  · linarith only [h2110, h2397, hlam]
                                  · linarith only [h2314, h2397, hlam]
                                · linarith only [h2310, h2396, hlam]
                              · linarith only [h2395, hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              rcases p2319_3 (m.d 0 3) (by simp) with h2402 | h2402
                              · linarith only [h1845, h2402, hlam]
                              · rcases p2319_3 (m.d 1 3) (by simp) with h2404 | h2404
                                · rcases p2319_3 (m.d 2 3) (by simp) with h2405 | h2405
                                  · linarith only [h2307, h2405, hlam]
                                  · rcases p2319_3 (m.d 3 4) (by simp) with h2407 | h2407
                                    · linarith only [h2309, h2407, hlam]
                                    · rcases p2319_3 (m.d 3 5) (by simp) with h2409 | h2409
                                      · linarith only [h2310, h2409, hlam]
                                      · rcases h3emin with h2411 | h2411 | h2411 | h2411 | h2411
                                        · linarith only [h2307, h2411, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2319_1]
                                        · rcases h4bigk with h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c | h2413c
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [hlam, p2413_0]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2308, h2313, hc34, hlam, hphi, p2413_1, u4elo0]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h1845, h2109, h2307, h2313, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2319_1, p2413_1]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h1845, h2109, h2307, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2319_1, p2413_1]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2114, hlam, p2413_0]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2109, hlam, p2413_1]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [hlam, p2413_0]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2413_1, u4elo1]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h1845, h2109, h2307, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2319_1, p2413_1]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2311, hlam, p2413_0]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2111, hlam, p2413_1]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2308, hlam, p2413_1]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [hlam, p2413_0]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2413_1, u4elo2]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2315, hlam, p2413_0]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2112, hlam, p2413_1]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2309, hlam, p2413_0]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2313, hlam, p2413_0]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [hlam, p2413_0]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2317, hlam, p2413_0]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2413_1, u4elo4]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2308, hc24, hlam, hphi, p2413_1, u4elo4]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2413_1, u4elo4]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2413_1, u4elo4]
                                          · have p2413_0 := h2413c.1
                                            have p2413_1 := h2413c.2.1
                                            have p2413_2 := h2413c.2.2.1
                                            have p2413_3 := h2413c.2.2.2
                                            linarith only [hlam, p2413_0]
                                        · linarith only [h2110, h2307, h2411, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2319_1]
                                        · linarith only [h2109, h2308, h2313, h2411, hlam, ht34, u4elo0]
                                        · linarith only [h2113, h2307, h2411, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2319_1]
                                · linarith only [h1845, h2404, hlam]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              rcases p2319_3 (m.d 0 3) (by simp) with h2444 | h2444
                              · linarith only [h1845, h2444, hlam]
                              · linarith only [h2110, h2444, hlam]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              rcases p2319_3 (m.d 0 3) (by simp) with h2447 | h2447
                              · linarith only [h1845, h2447, hlam]
                              · linarith only [h2112, h2447, hlam]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              rcases p2319_3 (m.d 0 3) (by simp) with h2450 | h2450
                              · linarith only [h1845, h2450, hlam]
                              · linarith only [h2113, h2450, hlam]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [h2110, hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [h2307, hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              rcases p2319_3 (m.d 0 3) (by simp) with h2456 | h2456
                              · rcases p2319_3 (m.d 1 3) (by simp) with h2457 | h2457
                                · rcases p2319_3 (m.d 2 3) (by simp) with h2458 | h2458
                                  · rcases p2319_3 (m.d 3 4) (by simp) with h2459 | h2459
                                    · linarith only [h2459, hlam, p2319_0]
                                    · rcases p2319_3 (m.d 3 5) (by simp) with h2461 | h2461
                                      · linarith only [h2314, h2461, hlam]
                                      · linarith only [h2317, h2461, hlam]
                                  · linarith only [h2458, hlam, p2319_0]
                                · linarith only [h2309, h2457, hlam]
                              · linarith only [h2112, h2456, hlam]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              rcases p2319_3 (m.d 0 3) (by simp) with h2467 | h2467
                              · rcases p2319_3 (m.d 1 3) (by simp) with h2468 | h2468
                                · rcases p2319_3 (m.d 2 3) (by simp) with h2469 | h2469
                                  · rcases p2319_3 (m.d 3 4) (by simp) with h2470 | h2470
                                    · linarith only [h2313, h2470, hlam]
                                    · rcases p2319_3 (m.d 3 5) (by simp) with h2472 | h2472
                                      · linarith only [h2472, hlam, p2319_0]
                                      · rcases h3emin with h2474 | h2474 | h2474 | h2474 | h2474
                                        · rcases h4bigk with h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c | h2475c
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [hlam, p2475_0]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2114, hc14, hlam, hphi, p2475_1, u4elo4]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2114, h2313, hc34, hlam, hphi, p2475_1, u4elo4]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2114, hc34, hlam, hphi, p2475_1, u4elo4]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2114, hlam, p2475_0]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2109, hlam, p2475_1]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [hlam, p2475_0]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2475_1, u4elo1]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2109, h2114, hc34, hlam, hphi, p2475_1, u4elo4]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2311, hlam, p2475_0]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2111, hlam, p2475_1]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2308, hlam, p2475_1]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [hlam, p2475_0]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2475_1, u4elo2]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2315, hlam, p2475_0]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2112, hlam, p2475_1]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2309, hlam, p2475_0]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2313, hlam, p2475_0]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [hlam, p2475_0]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2317, hlam, p2475_0]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2475_1, u4elo4]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2308, hc24, hlam, hphi, p2475_1, u4elo4]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2475_1, u4elo4]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2475_1, u4elo4]
                                          · have p2475_0 := h2475c.1
                                            have p2475_1 := h2475c.2.1
                                            have p2475_2 := h2475c.2.2.1
                                            have p2475_3 := h2475c.2.2.2
                                            linarith only [hlam, p2475_0]
                                        · rcases h4bigk with h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c | h2501c
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [hlam, p2501_0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2308, h2313, hc34, hlam, hphi, p2501_1, u4elo0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2501_1, u4elo0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2501_1, u4elo0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2114, hlam, p2501_0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2109, hlam, p2501_1]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [hlam, p2501_0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2501_1, u4elo1]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2109, h2114, hc34, hlam, hphi, p2501_1, u4elo4]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2311, hlam, p2501_0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2111, hlam, p2501_1]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2308, hlam, p2501_1]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [hlam, p2501_0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2501_1, u4elo2]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2315, hlam, p2501_0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2112, hlam, p2501_1]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2309, hlam, p2501_0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2313, hlam, p2501_0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [hlam, p2501_0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2317, hlam, p2501_0]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2501_1, u4elo4]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [hc14, hlam, hphi, p2501_1, u4elo4]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2501_1, u4elo4]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2501_1, u4elo4]
                                          · have p2501_0 := h2501c.1
                                            have p2501_1 := h2501c.2.1
                                            have p2501_2 := h2501c.2.2.1
                                            have p2501_3 := h2501c.2.2.2
                                            linarith only [hlam, p2501_0]
                                        · rcases h4bigk with h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c | h2527c
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [hlam, p2527_0]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2114, h2308, h2313, hc34, hlam, hphi, p2527_1, u4elo4]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2114, h2313, hc34, hlam, hphi, p2527_1, u4elo4]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2114, hc34, hlam, hphi, p2527_1, u4elo4]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2114, hlam, p2527_0]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2109, hlam, p2527_1]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [hlam, p2527_0]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2527_1, u4elo1]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2109, h2114, hc34, hlam, hphi, p2527_1, u4elo4]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2311, hlam, p2527_0]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2111, hlam, p2527_1]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2308, hlam, p2527_1]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [hlam, p2527_0]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2527_1, u4elo2]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2315, hlam, p2527_0]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2112, hlam, p2527_1]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2309, hlam, p2527_0]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2313, hlam, p2527_0]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [hlam, p2527_0]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2317, hlam, p2527_0]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2527_1, u4elo4]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2308, hc24, hlam, hphi, p2527_1, u4elo4]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [h2313, hc34, hlam, hphi, p2527_1, u4elo4]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2527_1, u4elo4]
                                          · have p2527_0 := h2527c.1
                                            have p2527_1 := h2527c.2.1
                                            have p2527_2 := h2527c.2.2.1
                                            have p2527_3 := h2527c.2.2.2
                                            linarith only [hlam, p2527_0]
                                        · linarith only [h2110, h2317, h2474, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p2319_1]
                                        · linarith only [h2110, h2474, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p2319_1]
                                  · linarith only [h2469, hlam, p2319_0]
                                · linarith only [h2310, h2468, hlam]
                              · linarith only [h2113, h2467, hlam]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [h2112, hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [h2309, hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [h2313, hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [h2317, hlam, p2319_1]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [h2113, hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [h2310, hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [h2314, hlam, p2319_0]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [h2113, h2114, hc34, hlam, hphi, p2319_1, u4elo4]
                            · have p2319_0 := h2319c.1
                              have p2319_1 := h2319c.2.1
                              have p2319_2 := h2319c.2.2.1
                              have p2319_3 := h2319c.2.2.2
                              linarith only [hlam, p2319_0]
                      · linarith only [h2113, h2114, h2313, h2314, hc34, hlam, hphi, u4elo4]
                    · linarith only [h2112, h2114, h2313, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h1845, h2113, h2114, h2310, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · linarith only [h1845, h2309, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h0, h2109, h2308, hc14, hlam, hphi, u4elo2]
          · linarith only [h0, h2109, h2110, h2307, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2574 | h2574
        · linarith only [h1845, h2109, h2113, h2574, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2576 | h2576
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2577 | h2577
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2578 | h2578
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2579 | h2579
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2580 | h2580
                  · linarith only [h1845, h2109, h2113, h2574, h2579, h2580, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h1845, h2109, h2113, h2577, h2579, h2580, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2583 | h2583
                  · linarith only [h1845, h2109, h2579, h2583, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h1845, h2109, h2579, h2583, hc14, hlam, hphi, u4elo4]
              · linarith only [h1845, h2109, h2577, h2578, hc24, hlam, hphi, u4elo3]
            · linarith only [h1845, h2109, h2576, h2577, hc14, hlam, hphi, u4elo2]
          · linarith only [h0, h2110, h2576, hlam]
    · linarith only [h1845, h2109, h2112, hc14, hlam, hphi, u4elo3]
  · linarith only [h2110, h2111, hc23, hlam, hphi, ht34, u4elo2]

end R2N4
