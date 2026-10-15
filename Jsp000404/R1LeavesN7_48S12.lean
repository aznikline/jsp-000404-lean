import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_48S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1719 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2158 | h2158
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2159 | h2159
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2160 | h2160
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2161 | h2161
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2162 | h2162
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2163 | h2163
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2164 | h2164
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2165 | h2165
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2166 | h2166
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2167 | h2167
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2168 | h2168
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2169 | h2169
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2170 | h2170
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2171 | h2171
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2172 | h2172
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2173 | h2173
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2174 | h2174
                                  · linarith only [h2159, h2171, h2174, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h0, h2158, h2170, h2174, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · linarith only [h1719, h2158, h2165, h2168, h2170, h2173, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h1719, h2158, h2165, h2168, h2169, h2172, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2179 | h2179
                              · linarith only [h0, h2159, h2162, h2171, h2179, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h1719, h2158, h2165, h2168, h2169, h2179, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h1719, h2158, h2164, h2170, hc04, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h1719, h2158, h2159, h2163, h2167, h2168, h2169, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h1719, h2158, h2159, h2162, h2167, h2168, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h2167, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h2160, h2166, hlam]
                · linarith only [h0, h2158, h2165, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h1719, h2158, h2164, hlam]
            · linarith only [h1719, h2158, h2162, h2163, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2190 | h2190
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2191 | h2191
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2192 | h2192
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2193 | h2193
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2194 | h2194
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2195 | h2195
                      · linarith only [h2162, h2190, h2192, h2195, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2197 | h2197
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2198 | h2198
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2199 | h2199
                            · linarith only [h0, h2159, h2195, h2199, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2201 | h2201
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2202 | h2202
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2203 | h2203
                                  · rcases h0bigk with h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c | h2204c
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [hlam, p2204_0]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h0, hlam, p2204_1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h1719, h2193, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2204_1, u2elo1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h1719, hlam, p2204_1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h1719, h2193, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2204_1, u2elo1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p2204_1, u2elo1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [hlam, p2204_0]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h0, h2159, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2204_1, u2elo1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h0, h1719, h2158, h2194, h2201, h2203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2204_1, u2elo1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h0, h2158, h2194, h2201, h2203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2204_1, u2elo1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h2158, h2194, h2201, h2203, hc03, hc45, hlam, hphi, ht0b, ht5b, p2204_1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h2159, hlam, p2204_1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [hlam, p2204_0]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h2162, hlam, p2204_1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h1719, h2158, h2162, h2193, h2194, h2201, h2203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2204_1, u2elo1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h1719, h2158, h2193, h2194, h2201, h2203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2204_1, u2elo1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h2160, hlam, p2204_0]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h1719, h2193, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2204_1, u2elo1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [hlam, p2204_0]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h1719, h2158, h2193, h2194, h2201, h2203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2204_1, u2elo1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h2158, hlam, p2204_0]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h2161, hlam, p2204_1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h2190, hlam, p2204_0]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [h2191, hlam, p2204_1]
                                    · have p2204_0 := h2204c.1
                                      have p2204_1 := h2204c.2.1
                                      have p2204_2 := h2204c.2.2.1
                                      have p2204_3 := h2204c.2.2.2
                                      linarith only [hlam, p2204_0]
                                  · linarith only [h1719, h2191, h2195, h2203, hlam]
                                · linarith only [h0, h2158, h2198, h2202, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h2162, h2190, h2201, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h1719, h2160, h2191, h2198, hc01, hc12, hlam, hphi]
                        · linarith only [h2162, h2190, h2197, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h2194, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h2158, h2193, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h0, h2158, h2192, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h1719, h2158, h2191, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2239 | h2239
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2240 | h2240
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2241 | h2241
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2242 | h2242
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2243 | h2243
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2244 | h2244
                        · linarith only [h1719, h2158, h2159, h2162, h2190, h2240, h2243, h2244, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h2159, h2162, h2243, h2244, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2247 | h2247
                        · linarith only [h2159, h2190, h2243, h2247, hc23, hc34, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2249 | h2249
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2250 | h2250
                            · linarith only [h1719, h2158, h2240, h2243, h2247, h2250, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2252 | h2252
                              · linarith only [h0, h2158, h2190, h2240, h2247, h2252, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2254 | h2254
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2255 | h2255
                                  · rcases h0bigk with h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [hlam, p2256_0]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h0, hlam, p2256_1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h1719, h2159, h2241, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2256_1, u2elo1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h1719, hlam, p2256_1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h1719, h2241, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2256_1, u2elo1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p2256_1, u2elo1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [hlam, p2256_0]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h0, h2159, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2256_1, u2elo1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2256_1, u2elo1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h0, h2158, h2247, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2256_1, u2elo1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h2158, h2240, h2247, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2256_1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h2159, hlam, p2256_1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [hlam, p2256_0]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h2162, hlam, p2256_1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h2190, hlam, p2256_1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h2158, h2240, h2247, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2256_1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h2160, hlam, p2256_0]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h1719, h2241, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2256_1, u2elo1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [hlam, p2256_0]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h1719, h2158, h2240, h2241, h2247, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2256_1, u2elo1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h2158, hlam, p2256_0]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h2161, hlam, p2256_1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h0, h2158, h2159, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2256_1, u2elo1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [h2239, hlam, p2256_1]
                                    · have p2256_0 := h2256c.1
                                      have p2256_1 := h2256c.2.1
                                      have p2256_2 := h2256c.2.2.1
                                      have p2256_3 := h2256c.2.2.2
                                      linarith only [hlam, p2256_0]
                                  · linarith only [h1719, h2243, h2254, h2255, hc01, hlam, hphi, ht12, u2elo4]
                                · linarith only [h0, h2158, h2249, h2254, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h1719, h2158, h2240, h2247, h2249, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1719, h2241, h2242, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h2158, h2241, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h0, h2158, h2240, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h1719, h2158, h2239, hlam]
        · linarith only [h0, h2158, h2161, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2290 | h2290
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2291 | h2291
          · linarith only [h2159, h2160, h2291, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2293 | h2293
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2294 | h2294
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2295 | h2295
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2296 | h2296
                  · linarith only [h0, h2160, h2296, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2158, h2296, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h0, h2158, h2159, h2295, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h1719, h2158, h2294, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2301 | h2301
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2302 | h2302
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2303 | h2303
                  · linarith only [h2160, h2303, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2158, h2303, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h0, h2158, h2159, h2302, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h1719, h2158, h2301, hlam]
        · linarith only [h0, h2158, h2290, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2309 | h2309
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2310 | h2310
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2311 | h2311
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2312 | h2312
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2313 | h2313
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2314 | h2314
                · linarith only [h1719, h2159, h2309, h2314, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2158, h2314, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h1719, h2158, h2313, hlam]
            · linarith only [h1719, h2158, h2159, h2309, h2312, hlam]
          · linarith only [h2159, h2309, h2311, hlam]
        · linarith only [h1719, h2158, h2309, h2310, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2321 | h2321
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2322 | h2322
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2323 | h2323
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2324 | h2324
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2325 | h2325
                · linarith only [h2159, h2325, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h2158, h2325, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h0, h2158, h2309, h2324, hlam]
            · linarith only [h0, h2158, h2309, h2322, h2323, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2330 | h2330
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2331 | h2331
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2332 | h2332
                · linarith only [h0, h2158, h2159, h2332, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h2158, h2332, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h1719, h2158, h2331, hlam]
            · linarith only [h0, h2158, h2159, h2330, hlam]
        · linarith only [h0, h2158, h2321, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2338 | h2338
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2339 | h2339
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2340 | h2340
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2341 | h2341
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2342 | h2342
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2343 | h2343
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2344 | h2344
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2345 | h2345
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2346 | h2346
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2347 | h2347
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2348 | h2348
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2349 | h2349
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2350 | h2350
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2351 | h2351
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2352 | h2352
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2353 | h2353
                                  · linarith only [h2338, h2350, h2353, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h0, h2338, h2350, h2352, h2353, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2356 | h2356
                                  · linarith only [h0, h2338, h2341, h2352, h2356, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases h0bigk with h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c | h2358c
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [hlam, p2358_0]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h0, hlam, p2358_1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h2158, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2358_1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h1719, hlam, p2358_1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h2158, hlam, p2358_1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p2358_1, u2elo1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [hlam, p2358_0]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2358_1, u2elo1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h0, h1719, hc01, hlam, hphi, ht12, p2358_1, u2elo1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2358_1, u2elo1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h0, h2338, hc01, hlam, hphi, ht12, p2358_1, u2elo1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h2338, hlam, p2358_1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [hlam, p2358_0]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h2343, h2350, h2352, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2358_1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h0, h2338, h2343, h2350, h2352, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2358_1, u2elo1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h1719, hc01, hc14, hlam, hphi, p2358_1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h2339, hlam, p2358_0]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h2341, hlam, p2358_0]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [hlam, p2358_0]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h0, h2338, h2341, h2343, h2350, h2352, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2358_1, u2elo1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h2158, h2349, hc01, hc14, hlam, hphi, p2358_1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h2340, hlam, p2358_1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h2342, hlam, p2358_0]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [h2343, hlam, p2358_1]
                                    · have p2358_0 := h2358c.1
                                      have p2358_1 := h2358c.2.1
                                      have p2358_2 := h2358c.2.2.1
                                      have p2358_3 := h2358c.2.2.2
                                      linarith only [hlam, p2358_0]
                              · linarith only [h0, h2338, h2342, h2350, h2351, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2385 | h2385
                              · linarith only [h0, h2338, h2341, h2350, h2385, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2387 | h2387
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2388 | h2388
                                  · rcases h0bigk with h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c | h2389c
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [hlam, p2389_0]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h0, hlam, p2389_1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h2341, h2385, h2388, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2389_1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h1719, hlam, p2389_1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h2158, hlam, p2389_1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p2389_1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [hlam, p2389_0]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h0, h2341, h2385, h2388, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2389_1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2389_1, u2elo1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h0, h2158, hc01, hlam, hphi, ht12, p2389_1, u2elo1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h0, h2338, hc01, hlam, hphi, ht12, p2389_1, u2elo1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h2338, hlam, p2389_1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [hlam, p2389_0]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h0, h2338, h2341, h2385, h2388, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2389_1, u2elo1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h0, h2338, h2342, h2385, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2389_1, u2elo1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h1719, h2344, h2347, hc01, hlam, hphi, ht12, p2389_1, u2elo1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h2339, hlam, p2389_0]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h2341, hlam, p2389_0]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [hlam, p2389_0]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h1719, h2342, h2344, h2347, h2385, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2389_1, u2elo1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h2158, h2344, h2347, h2349, hc01, hlam, hphi, ht12, p2389_1, u2elo1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h2340, hlam, p2389_1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h2342, hlam, p2389_0]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [h2343, hlam, p2389_1]
                                    · have p2389_0 := h2389c.1
                                      have p2389_1 := h2389c.2.1
                                      have p2389_2 := h2389c.2.2.1
                                      have p2389_3 := h2389c.2.2.2
                                      linarith only [hlam, p2389_0]
                                  · linarith only [h1719, h2343, h2344, h2347, h2350, h2388, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2416 | h2416
                                  · linarith only [h0, h2338, h2341, h2387, h2416, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · linarith only [h1719, h2343, h2344, h2347, h2350, h2416, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h1719, h2343, h2349, hlam]
                        · linarith only [h0, h1719, h2338, h2342, h2343, h2347, h2348, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h1719, h2341, h2347, hlam]
                    · linarith only [h0, h2346, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h2345, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2344, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2425 | h2425
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2426 | h2426
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2427 | h2427
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2428 | h2428
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2429 | h2429
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2430 | h2430
                          · linarith only [h1719, h2343, h2425, h2428, h2430, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2432 | h2432
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2433 | h2433
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2434 | h2434
                                · linarith only [h1719, h2430, h2434, hc01, hlam, hphi, ht12, u2elo3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2436 | h2436
                                  · linarith only [h0, h1719, h2338, h2430, h2432, h2436, hc01, hlam, hphi, ht12, u2elo1]
                                  · rcases h0bigk with h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c | h2438c
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [hlam, p2438_0]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h0, hlam, p2438_1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h1719, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2438_1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h1719, hlam, p2438_1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h2158, hlam, p2438_1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p2438_1, u2elo1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [hlam, p2438_0]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2438_1, u2elo1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2438_1, u2elo1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2438_1, u2elo1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h0, h2338, hc01, hlam, hphi, ht12, p2438_1, u2elo1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h2338, hlam, p2438_1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [hlam, p2438_0]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h0, h1719, h2338, hc01, hlam, hphi, ht12, p2438_1, u2elo1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h0, h2338, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2438_1, u2elo1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h1719, h2430, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2438_1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h2339, hlam, p2438_0]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h2341, hlam, p2438_0]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [hlam, p2438_0]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h2343, hlam, p2438_0]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h2158, h2425, h2429, hc01, hlam, hphi, ht12, p2438_1, u2elo1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h2340, hlam, p2438_1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h2342, hlam, p2438_0]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [h2158, h2425, h2429, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2438_1, u2elo1]
                                    · have p2438_0 := h2438c.1
                                      have p2438_1 := h2438c.2.1
                                      have p2438_2 := h2438c.2.2.1
                                      have p2438_3 := h2438c.2.2.2
                                      linarith only [hlam, p2438_0]
                              · linarith only [h0, h2338, h2342, h2432, h2433, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2465 | h2465
                              · linarith only [h0, h2338, h2341, h2432, h2465, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2467 | h2467
                                · linarith only [h1719, h2430, h2467, hc01, hlam, hphi, ht12, u2elo3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2469 | h2469
                                  · linarith only [h0, h1719, h2338, h2341, h2430, h2469, hc01, hlam, hphi, ht12, u2elo1]
                                  · rcases h0bigk with h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c | h2471c
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [hlam, p2471_0]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h0, hlam, p2471_1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h2342, h2432, h2469, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2471_1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h1719, hlam, p2471_1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h2158, hlam, p2471_1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p2471_1, u2elo1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [hlam, p2471_0]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h0, h2342, h2432, h2469, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2471_1, u2elo1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h0, h2341, h2432, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2471_1, u2elo1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2471_1, u2elo1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h0, h2338, hc01, hlam, hphi, ht12, p2471_1, u2elo1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h2338, hlam, p2471_1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [hlam, p2471_0]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h0, h2338, h2341, h2432, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2471_1, u2elo1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h0, h2338, h2342, h2432, h2469, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2471_1, u2elo1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h1719, h2430, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2471_1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h2339, hlam, p2471_0]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h2341, hlam, p2471_0]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [hlam, p2471_0]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h2343, hlam, p2471_0]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h2158, h2425, h2429, hc01, hlam, hphi, ht12, p2471_1, u2elo1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h2340, hlam, p2471_1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h2342, hlam, p2471_0]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [h2158, h2425, h2429, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2471_1, u2elo1]
                                    · have p2471_0 := h2471c.1
                                      have p2471_1 := h2471c.2.1
                                      have p2471_2 := h2471c.2.2.1
                                      have p2471_3 := h2471c.2.2.2
                                      linarith only [hlam, p2471_0]
                        · linarith only [h0, h2338, h2342, h2428, h2429, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h1719, h2341, h2428, hlam]
                    · linarith only [h0, h2427, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h2426, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2425, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2502 | h2502
              · linarith only [h2341, h2342, h2502, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2504 | h2504
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2505 | h2505
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2506 | h2506
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2507 | h2507
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2508 | h2508
                        · linarith only [h2341, h2342, h2504, h2508, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2510 | h2510
                          · linarith only [h1719, h2502, h2506, h2507, h2508, h2510, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2512 | h2512
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2513 | h2513
                              · linarith only [h0, h2338, h2508, h2513, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2515 | h2515
                                · linarith only [h1719, h2510, h2515, hc01, hlam, hphi, ht12, u2elo3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2517 | h2517
                                  · linarith only [h1719, h2510, h2517, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · rcases h0bigk with h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c
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
                                      linarith only [h1719, h2507, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2519_1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h1719, hlam, p2519_1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h2158, hlam, p2519_1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p2519_1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [hlam, p2519_0]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2519_1, u2elo1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h0, h1719, hc01, hlam, hphi, ht12, p2519_1, u2elo1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h0, h2158, hc01, hlam, hphi, ht12, p2519_1, u2elo1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h0, h2338, hc01, hlam, hphi, ht12, p2519_1, u2elo1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h2338, hlam, p2519_1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [hlam, p2519_0]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h0, h1719, h2338, hc01, hlam, hphi, ht12, p2519_1, u2elo1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h2342, hlam, p2519_1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h1719, h2507, h2508, h2517, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2519_1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h2339, hlam, p2519_0]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h2341, hlam, p2519_0]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [hlam, p2519_0]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h2502, hlam, p2519_0]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h2158, h2506, hc01, hlam, hphi, ht12, p2519_1, u2elo1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h2340, hlam, p2519_1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h2158, h2506, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2519_1, u2elo1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [h2158, h2506, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2519_1, u2elo1]
                                    · have p2519_0 := h2519c.1
                                      have p2519_1 := h2519c.2.1
                                      have p2519_2 := h2519c.2.2.1
                                      have p2519_3 := h2519c.2.2.2
                                      linarith only [hlam, p2519_0]
                            · linarith only [h2341, h2342, h2512, hc23, hc35, hlam, hphi]
                      · linarith only [h2341, h2342, h2507, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h2506, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h2505, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2504, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2550 | h2550
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2551 | h2551
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2552 | h2552
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2553 | h2553
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2554 | h2554
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2555 | h2555
                      · linarith only [h2341, h2550, h2552, h2555, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2557 | h2557
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2558 | h2558
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2559 | h2559
                            · linarith only [h2338, h2341, h2559, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2561 | h2561
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2562 | h2562
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2563 | h2563
                                  · rcases h0bigk with h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c | h2564c
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [hlam, p2564_0]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h0, hlam, p2564_1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h2158, h2557, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2564_1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h1719, hlam, p2564_1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h2158, hlam, p2564_1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, p2564_1, u2elo0]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [hlam, p2564_0]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h0, h2338, h2561, h2563, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2564_1, u2elo1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h0, h2338, h2341, h2561, h2563, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2564_1, u2elo1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2564_1, u2elo1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h1719, h2341, h2553, hc01, hlam, hphi, ht12, p2564_1, u2elo1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h2338, hlam, p2564_1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [hlam, p2564_0]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h2341, hlam, p2564_1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h1719, h2158, h2341, h2553, hc01, hlam, hphi, ht12, p2564_1, u2elo1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h1719, h2553, hc01, hlam, hphi, ht12, p2564_1, u2elo1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h2339, hlam, p2564_0]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h1719, h2553, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2564_1, u2elo1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [hlam, p2564_0]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h1719, h2158, h2553, hc01, hlam, hphi, ht12, p2564_1, u2elo1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h2158, h2553, h2555, h2557, hc01, hlam, hphi, ht12, p2564_1, u2elo1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h2340, hlam, p2564_1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h2550, hlam, p2564_0]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [h2551, hlam, p2564_1]
                                    · have p2564_0 := h2564c.1
                                      have p2564_1 := h2564c.2.1
                                      have p2564_2 := h2564c.2.2.1
                                      have p2564_3 := h2564c.2.2.2
                                      linarith only [hlam, p2564_0]
                                  · linarith only [h2158, h2555, h2557, h2563, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h2339, h2551, h2559, h2561, h2562, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h2341, h2550, h2561, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h1719, h2339, h2551, h2558, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h2341, h2550, h2557, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h2554, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h2553, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2552, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2341, h2550, h2551, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2599 | h2599
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2600 | h2600
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2601 | h2601
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2602 | h2602
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2603 | h2603
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2604 | h2604
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2605 | h2605
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2606 | h2606
                            · linarith only [h2338, h2341, h2606, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2608 | h2608
                              · linarith only [h2338, h2550, h2608, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2610 | h2610
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2611 | h2611
                                  · rcases h0bigk with h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c | h2612c
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [hlam, p2612_0]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h0, hlam, p2612_1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2158, h2605, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2612_1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h1719, hlam, p2612_1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2158, hlam, p2612_1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, p2612_1, u2elo0]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [hlam, p2612_0]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h0, h2338, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2612_1, u2elo1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2612_1, u2elo1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h0, h2158, hc01, hlam, hphi, ht12, p2612_1, u2elo1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h0, h2338, hc01, hlam, hphi, ht12, p2612_1, u2elo1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2338, hlam, p2612_1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [hlam, p2612_0]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2341, hlam, p2612_1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2550, hlam, p2612_1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h1719, h2600, h2603, hc01, hlam, hphi, ht12, p2612_1, u2elo1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2339, hlam, p2612_0]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2341, h2600, h2603, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2612_1, u2elo1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [hlam, p2612_0]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2341, h2600, h2603, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2612_1, u2elo1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2158, h2600, h2603, h2605, hc01, hlam, hphi, ht12, p2612_1, u2elo1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2340, hlam, p2612_1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2338, h2550, h2600, h2603, h2611, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2612_1, u2elo1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [h2599, hlam, p2612_1]
                                    · have p2612_0 := h2612c.1
                                      have p2612_1 := h2612c.2.1
                                      have p2612_2 := h2612c.2.2.1
                                      have p2612_3 := h2612c.2.2.2
                                      linarith only [hlam, p2612_0]
                                  · linarith only [h1719, h2341, h2610, h2611, hc01, hlam, hphi, ht12, u2elo3]
                                · linarith only [h2341, h2599, h2600, h2603, h2610, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h2341, h2599, h2600, h2603, h2605, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h2338, h2341, h2603, h2604, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2642 | h2642
                        · linarith only [h2338, h2550, h2603, h2642, hc23, hc34, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2644 | h2644
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2645 | h2645
                            · linarith only [h0, h2338, h2603, h2645, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2647 | h2647
                              · linarith only [h2158, h2642, h2647, hc01, hlam, hphi, ht12, u2elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2649 | h2649
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2650 | h2650
                                  · rcases h0bigk with h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c | h2651c
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [hlam, p2651_0]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h0, hlam, p2651_1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2651_1, u2elo1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h1719, hlam, p2651_1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h2158, hlam, p2651_1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p2651_1, u2elo1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [hlam, p2651_0]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2651_1, u2elo1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2651_1, u2elo1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h0, h2158, hc01, hlam, hphi, ht12, p2651_1, u2elo1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h0, h2338, hc01, hlam, hphi, ht12, p2651_1, u2elo1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h2338, hlam, p2651_1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [hlam, p2651_0]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h2341, hlam, p2651_1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h2550, hlam, p2651_1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h1719, h2601, hc01, hlam, hphi, ht12, p2651_1, u2elo1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h2339, hlam, p2651_0]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h1719, h2601, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2651_1, u2elo1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [hlam, p2651_0]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h1719, h2158, h2601, hc01, hlam, hphi, ht12, p2651_1, u2elo1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h2158, hc01, hc15, hlam, hphi, p2651_1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h2340, hlam, p2651_1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h0, h2338, h2340, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2651_1, u2elo1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [h2599, hlam, p2651_1]
                                    · have p2651_0 := h2651c.1
                                      have p2651_1 := h2651c.2.1
                                      have p2651_2 := h2651c.2.2.1
                                      have p2651_3 := h2651c.2.2.2
                                      linarith only [hlam, p2651_0]
                                  · linarith only [h2341, h2599, h2650, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2678 | h2678
                                  · rcases h0bigk with h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h0, hlam, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h0, h2338, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2679_1, u2elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h1719, hlam, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2158, hlam, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p2679_1, u2elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h0, h2338, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2679_1, u2elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h0, h2599, h2645, h2649, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2679_1, u2elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2679_1, u2elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h0, h2338, hc01, hlam, hphi, ht12, p2679_1, u2elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2338, hlam, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2341, hlam, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2550, hlam, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h1719, hc01, hc14, hlam, hphi, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2339, hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h0, h2339, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2679_1, u2elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h0, h2339, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2679_1, u2elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2158, h2644, hc01, hc14, hlam, hphi, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2340, hlam, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h0, h2338, h2340, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2679_1, u2elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2599, hlam, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [hlam, p2679_0]
                                  · linarith only [h2341, h2599, h2678, hlam]
                          · linarith only [h1719, h2599, h2644, hlam]
                    · linarith only [h0, h2602, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h2601, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2600, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2710 | h2710
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2711 | h2711
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2712 | h2712
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2713 | h2713
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2714 | h2714
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2715 | h2715
                          · linarith only [h1719, h2599, h2711, h2715, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2717 | h2717
                            · linarith only [h2338, h2341, h2717, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2719 | h2719
                              · linarith only [h2338, h2341, h2550, h2710, h2713, h2719, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2721 | h2721
                                · linarith only [h1719, h2715, h2721, hc01, hlam, hphi, ht12, u2elo3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2723 | h2723
                                  · linarith only [h1719, h2715, h2723, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · rcases h0bigk with h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c
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
                                      linarith only [h1719, h2338, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2725_1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h1719, hlam, p2725_1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2158, hlam, p2725_1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p2725_1, u2elo1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [hlam, p2725_0]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h0, h2338, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2725_1, u2elo1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2725_1, u2elo1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2725_1, u2elo1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2341, hc01, hc34, hlam, hphi, ht12, ht23, p2725_1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2338, hlam, p2725_1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [hlam, p2725_0]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2341, hlam, p2725_1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2550, hlam, p2725_1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h1719, h2715, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2725_1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2339, hlam, p2725_0]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2158, h2599, h2710, h2714, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2725_1, u2elo1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [hlam, p2725_0]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2599, hlam, p2725_0]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2158, h2710, h2714, hc01, hlam, hphi, ht12, p2725_1, u2elo1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2340, hlam, p2725_1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2158, h2710, h2714, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2725_1, u2elo1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [h2158, h2710, h2714, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2725_1, u2elo1]
                                    · have p2725_0 := h2725c.1
                                      have p2725_1 := h2725c.2.1
                                      have p2725_2 := h2725c.2.2.1
                                      have p2725_3 := h2725c.2.2.2
                                      linarith only [hlam, p2725_0]
                        · linarith only [h2338, h2341, h2713, h2714, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2752 | h2752
                        · linarith only [h2338, h2550, h2713, h2752, hc23, hc34, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2754 | h2754
                          · linarith only [h1719, h2599, h2711, h2754, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2756 | h2756
                            · linarith only [h2338, h2341, h2756, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2758 | h2758
                              · linarith only [h1719, h2338, h2341, h2752, h2754, h2758, hc13, hc45, hlam, hphi, ht34]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2760 | h2760
                                · linarith only [h0, h1719, h2339, h2341, h2754, h2760, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2762 | h2762
                                  · linarith only [h1719, h2754, h2762, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · rcases h0bigk with h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h0, hlam, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h1719, h2338, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h1719, hlam, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2158, hlam, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p2764_1, u2elo1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h0, h2338, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2764_1, u2elo1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h0, h1719, hc01, hlam, hphi, ht12, p2764_1, u2elo1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2764_1, u2elo1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h0, h2338, hc01, hlam, hphi, ht12, p2764_1, u2elo1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2338, hlam, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2341, hlam, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2550, hlam, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h1719, h2713, h2762, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2339, hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h1719, h2713, h2762, hc03, hc45, hlam, hphi, ht34, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2599, hlam, p2764_0]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2158, h2712, hc01, hlam, hphi, ht12, p2764_1, u2elo1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2340, hlam, p2764_1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2158, h2338, h2712, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2764_1, u2elo1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [h2158, h2712, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2764_1, u2elo1]
                                    · have p2764_0 := h2764c.1
                                      have p2764_1 := h2764c.2.1
                                      have p2764_2 := h2764c.2.2.1
                                      have p2764_3 := h2764c.2.2.2
                                      linarith only [hlam, p2764_0]
                    · linarith only [h0, h2340, h2712, hlam]
                  · linarith only [h0, h2711, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2710, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2793 | h2793
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2794 | h2794
            · linarith only [h2338, h2340, h2794, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2796 | h2796
              · linarith only [h2339, h2340, h2796, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2798 | h2798
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2799 | h2799
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2800 | h2800
                    · linarith only [h2340, h2800, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h2800, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h2799, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h2338, h2340, h2798, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2805 | h2805
            · linarith only [h2339, h2340, h2793, h2805, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2807 | h2807
              · linarith only [h2339, h2340, h2807, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2809 | h2809
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2810 | h2810
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2811 | h2811
                    · linarith only [h2340, h2811, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h2811, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h2810, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2809, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2816 | h2816
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2817 | h2817
          · linarith only [h2338, h2339, h2817, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2819 | h2819
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2820 | h2820
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2821 | h2821
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2822 | h2822
                  · linarith only [h2338, h2339, h2822, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2822, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2821, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2338, h2339, h2819, h2820, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2827 | h2827
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2828 | h2828
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2829 | h2829
                  · linarith only [h2339, h2829, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2829, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2828, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2339, h2816, h2827, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2834 | h2834
          · linarith only [h2338, h2339, h2834, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2836 | h2836
            · linarith only [h2338, h2816, h2836, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2838 | h2838
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2839 | h2839
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2840 | h2840
                  · linarith only [h2339, h2840, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2840, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2839, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2844 | h2844
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2845 | h2845
                  · linarith only [h2339, h2845, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2845, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2844, hc01, hlam, hphi, ht12, u2elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2849 | h2849
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2850 | h2850
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2851 | h2851
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2852 | h2852
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2853 | h2853
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2854 | h2854
                · linarith only [h2338, h2854, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h2854, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2857 | h2857
                · linarith only [h2338, h2849, h2857, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h2857, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h2338, h2850, h2852, hlam]
          · linarith only [h2338, h2849, h2851, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2862 | h2862
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2863 | h2863
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2864 | h2864
              · linarith only [h2849, h2850, h2864, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2866 | h2866
                · linarith only [h2338, h2849, h2866, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h2866, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2869 | h2869
              · linarith only [h2338, h2849, h2863, h2869, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2871 | h2871
                · linarith only [h2338, h2849, h2871, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h2871, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h2338, h2849, h2862, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2875 | h2875
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2876 | h2876
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2877 | h2877
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2878 | h2878
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2879 | h2879
                · linarith only [h2338, h2879, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h2879, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2849, h2875, h2878, hlam]
            · linarith only [h2338, h2875, h2877, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2884 | h2884
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2885 | h2885
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2886 | h2886
                · linarith only [h2338, h2886, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h2886, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2338, h2875, h2876, h2885, hlam]
            · linarith only [h2338, h2875, h2884, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2891 | h2891
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2892 | h2892
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2893 | h2893
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2894 | h2894
                · linarith only [h2338, h2894, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h2894, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2897 | h2897
                · linarith only [h0, h2338, h2897, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2897, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2900 | h2900
              · linarith only [h2891, h2892, h2900, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2902 | h2902
                · linarith only [h0, h2338, h2902, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2902, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2905 | h2905
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2906 | h2906
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2907 | h2907
                · linarith only [h0, h2338, h2907, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2907, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2891, h2905, h2906, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2911 | h2911
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2912 | h2912
                · linarith only [h0, h2338, h2912, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2912, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2915 | h2915
                · linarith only [h0, h2338, h2915, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2915, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1719 | h1719
  · exact r1l7_20_12_14_H_I_L_0_L_I_x1_x0 m hb0 hb2 hb4 h0 h1719
  · exact r1l7_20_12_14_H_I_L_0_L_I_x1_x1 m hb0 hb2 hb4 h0 h1719

set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_H_I_L_0_L_I_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_H_I_L_0_L_I_x1 m hb0 hb2 hb4 h0

end R2N4
