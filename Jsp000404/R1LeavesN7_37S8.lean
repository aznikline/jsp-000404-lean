import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1695 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2185 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2186 | h2186
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2187 | h2187
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2188 | h2188
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2189 | h2189
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2190 | h2190
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2191 | h2191
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2192 | h2192
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2193 | h2193
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2194 | h2194
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2195 | h2195
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2196 | h2196
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2197 | h2197
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2198 | h2198
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2199 | h2199
                            · rcases h2bigk with h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h0, hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h2196, h2199, hc02, hc45, hlam, hphi, ht0b, ht5b, p2200_1]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                rcases p2200_3 (m.d 0 2) (by simp) with h2204 | h2204
                                · rcases p2200_3 (m.d 1 2) (by simp) with h2205 | h2205
                                  · rcases p2200_3 (m.d 2 3) (by simp) with h2206 | h2206
                                    · linarith only [h2186, h2206, hlam]
                                    · linarith only [h2196, h2206, hlam]
                                  · linarith only [h2192, h2205, hlam]
                                · linarith only [h2204, hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                rcases p2200_3 (m.d 0 2) (by simp) with h2211 | h2211
                                · rcases p2200_3 (m.d 1 2) (by simp) with h2212 | h2212
                                  · rcases p2200_3 (m.d 2 3) (by simp) with h2213 | h2213
                                    · linarith only [h2186, h2213, hlam]
                                    · linarith only [h2197, h2213, hlam]
                                  · linarith only [h0, h2185, h2192, h2198, h2212, hlam]
                                · linarith only [h2211, hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h0, h2185, h2192, h2196, h2199, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2200_1]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h2196, h2199, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2200_1]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                rcases p2200_3 (m.d 0 2) (by simp) with h2221 | h2221
                                · linarith only [h0, h2221, hlam]
                                · linarith only [h2187, h2221, hlam]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                rcases p2200_3 (m.d 0 2) (by simp) with h2224 | h2224
                                · linarith only [h0, h2224, hlam]
                                · linarith only [h2188, h2224, hlam]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h2186, hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h2191, hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h2186, h2196, h2199, hc02, hc45, hlam, hphi, ht0b, ht5b, p2200_1]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                rcases p2200_3 (m.d 0 2) (by simp) with h2231 | h2231
                                · rcases p2200_3 (m.d 1 2) (by simp) with h2232 | h2232
                                  · rcases p2200_3 (m.d 2 3) (by simp) with h2233 | h2233
                                    · rcases p2200_3 (m.d 2 4) (by simp) with h2234 | h2234
                                      · linarith only [h2196, h2234, hlam]
                                      · linarith only [h2198, h2234, hlam]
                                    · linarith only [h2197, h2233, hlam]
                                  · linarith only [h0, h2186, h2232, hlam, p2200_1]
                                · linarith only [h2188, h2231, hlam]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h2187, hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h2192, hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h2196, hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h1695, h2185, h2192, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p2200_1]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h2188, hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h1695, h2191, hc01, hc25, hlam, hphi, ht12, p2200_1]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h2197, hlam, p2200_0]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [h2198, hlam, p2200_1]
                              · have p2200_0 := h2200c.1
                                have p2200_1 := h2200c.2.1
                                have p2200_2 := h2200c.2.2.1
                                have p2200_3 := h2200c.2.2.2
                                linarith only [hlam, p2200_0]
                            · linarith only [h2190, h2199, hc34, hlam, hphi, u4elo0]
                          · linarith only [h1695, h2185, h2191, h2195, h2198, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1695, h2185, h2191, h2194, h2195, h2196, h2197, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2253 | h2253
                        · linarith only [h1695, h2185, h2191, h2193, h2196, h2253, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2255 | h2255
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2256 | h2256
                            · rcases h2bigk with h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h0, hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                rcases p2257_3 (m.d 0 2) (by simp) with h2260 | h2260
                                · rcases p2257_3 (m.d 1 2) (by simp) with h2261 | h2261
                                  · rcases p2257_3 (m.d 2 3) (by simp) with h2262 | h2262
                                    · linarith only [h2262, hlam, p2257_0]
                                    · rcases p2257_3 (m.d 2 4) (by simp) with h2264 | h2264
                                      · linarith only [h2187, h2264, hlam]
                                      · linarith only [h2196, h2264, hlam]
                                  · linarith only [h2191, h2261, hlam]
                                · linarith only [h2260, hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                rcases p2257_3 (m.d 0 2) (by simp) with h2269 | h2269
                                · rcases p2257_3 (m.d 1 2) (by simp) with h2270 | h2270
                                  · rcases p2257_3 (m.d 2 3) (by simp) with h2271 | h2271
                                    · linarith only [h2186, h2271, hlam]
                                    · rcases p2257_3 (m.d 2 4) (by simp) with h2273 | h2273
                                      · linarith only [h2273, hlam, p2257_0]
                                      · rcases p2257_3 (m.d 2 5) (by simp) with h2275 | h2275
                                        · linarith only [h2188, h2275, hlam]
                                        · rcases h4bigk with h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h2194, h2195, h2253, hc23, hlam, hphi, ht34, p2277_1, u4elo0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [hc24, hlam, hphi, p2277_1, u4elo0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2277_1, u4elo0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            rcases p2277_3 (m.d 0 4) (by simp) with h2282 | h2282
                                            · rcases p2277_3 (m.d 1 4) (by simp) with h2283 | h2283
                                              · linarith only [h2185, h2283, hlam]
                                              · linarith only [h2195, h2283, hlam]
                                            · linarith only [h2282, hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h2185, hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h1695, h2185, h2191, h2255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2277_1]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h1695, h2185, h2191, h2253, h2256, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2277_1]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h1695, h2185, h2191, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2277_1]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h2187, hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h2192, hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h2196, hlam, p2277_1]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [hc02, hc45, hlam, hphi, ht0b, ht5b, p2257_1, p2277_1]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h2189, hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h2193, hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [hc24, hlam, hphi, p2277_1, u4elo3]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h1695, h2185, h2191, h2193, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2277_1]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h2190, hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h2195, hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h2255, hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [h2256, hlam, p2277_0]
                                          · have p2277_0 := h2277c.1
                                            have p2277_1 := h2277c.2.1
                                            have p2277_2 := h2277c.2.2.1
                                            have p2277_3 := h2277c.2.2.2
                                            linarith only [hlam, p2277_0]
                                  · linarith only [h2192, h2270, hlam]
                                · linarith only [h2269, hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                rcases p2257_3 (m.d 0 2) (by simp) with h2309 | h2309
                                · rcases p2257_3 (m.d 1 2) (by simp) with h2310 | h2310
                                  · rcases p2257_3 (m.d 2 3) (by simp) with h2311 | h2311
                                    · linarith only [h2186, h2311, hlam]
                                    · rcases p2257_3 (m.d 2 4) (by simp) with h2313 | h2313
                                      · linarith only [h2187, h2313, hlam]
                                      · linarith only [h2255, h2313, hlam]
                                  · linarith only [h0, h2310, hlam, p2257_1]
                                · linarith only [h2309, hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h0, h2185, h2194, h2195, h2253, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2257_1]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h0, h2185, h2194, h2195, h2253, hlam, p2257_2]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                rcases p2257_3 (m.d 0 2) (by simp) with h2321 | h2321
                                · linarith only [h0, h2321, hlam]
                                · linarith only [h2187, h2321, hlam]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                rcases p2257_3 (m.d 0 2) (by simp) with h2324 | h2324
                                · linarith only [h0, h2324, hlam]
                                · linarith only [h2188, h2324, hlam]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h2186, hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h2191, hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h2196, hlam, p2257_1]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h2253, hlam, p2257_1]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h2187, hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h2192, hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, p2257_1, u4elo2]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h1695, h2185, h2191, h2192, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2257_1]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h2188, hlam, p2257_0]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h1695, h2191, hc01, hc25, hlam, hphi, ht12, p2257_1]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h1695, h2185, h2191, h2194, h2195, h2253, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2257_1]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [h2255, hlam, p2257_1]
                              · have p2257_0 := h2257c.1
                                have p2257_1 := h2257c.2.1
                                have p2257_2 := h2257c.2.2.1
                                have p2257_3 := h2257c.2.2.2
                                linarith only [hlam, p2257_0]
                            · linarith only [h2196, h2255, h2256, hlam]
                          · linarith only [h2190, h2255, hc24, hlam, hphi, u4elo0]
                    · linarith only [h2190, h2195, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2345 | h2345
                    · linarith only [h1695, h2185, h2194, h2345, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1695, h2185, h2190, h2194, h2345, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h1695, h2193, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h2185, h2192, hc14, hlam, hphi, u4elo2]
            · linarith only [h0, h2185, h2186, h2191, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2351 | h2351
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2352 | h2352
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2353 | h2353
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2354 | h2354
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2355 | h2355
                    · linarith only [h2190, h2355, hc04, hlam, hphi, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2357 | h2357
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2358 | h2358
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2359 | h2359
                          · linarith only [h2185, h2190, h2352, h2359, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2361 | h2361
                            · linarith only [h2185, h2190, h2352, h2357, h2361, hlam]
                            · rcases h2bigk with h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c | h2363c
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h0, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                rcases p2363_3 (m.d 0 2) (by simp) with h2366 | h2366
                                · rcases p2363_3 (m.d 1 2) (by simp) with h2367 | h2367
                                  · rcases p2363_3 (m.d 2 3) (by simp) with h2368 | h2368
                                    · linarith only [h2368, hlam, p2363_0]
                                    · rcases p2363_3 (m.d 2 4) (by simp) with h2370 | h2370
                                      · linarith only [h2187, h2370, hlam]
                                      · rcases p2363_3 (m.d 2 5) (by simp) with h2372 | h2372
                                        · linarith only [h2188, h2372, hlam]
                                        · rcases h4bigk with h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2190, h2352, hc24, hlam, hphi, p2374_1, u4elo4]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2190, hc24, hlam, hphi, p2374_1, u4elo4]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2190, hc34, hlam, hphi, p2374_1, u4elo4]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2190, hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2185, hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [hc24, hlam, hphi, p2374_1, u4elo1]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2185, h2190, hc34, hlam, hphi, p2374_1, u4elo4]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2355, hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2187, hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2352, hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2374_1, u4elo2]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2359, hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2189, hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2353, hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2357, hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2361, hlam, p2374_0]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2374_1, u4elo4]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2352, hc24, hlam, hphi, p2374_1, u4elo4]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [h2357, hc34, hlam, hphi, p2374_1, u4elo4]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2374_1, u4elo4]
                                          · have p2374_0 := h2374c.1
                                            have p2374_1 := h2374c.2.1
                                            have p2374_2 := h2374c.2.2.1
                                            have p2374_3 := h2374c.2.2.2
                                            linarith only [hlam, p2374_0]
                                  · linarith only [h2351, h2367, hlam]
                                · linarith only [h2366, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                rcases p2363_3 (m.d 0 2) (by simp) with h2402 | h2402
                                · rcases p2363_3 (m.d 1 2) (by simp) with h2403 | h2403
                                  · rcases p2363_3 (m.d 2 3) (by simp) with h2404 | h2404
                                    · linarith only [h2186, h2404, hlam]
                                    · linarith only [h2357, h2404, hlam]
                                  · linarith only [h2352, h2403, hlam]
                                · linarith only [h2402, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                rcases p2363_3 (m.d 0 2) (by simp) with h2409 | h2409
                                · rcases p2363_3 (m.d 1 2) (by simp) with h2410 | h2410
                                  · rcases p2363_3 (m.d 2 3) (by simp) with h2411 | h2411
                                    · linarith only [h2186, h2411, hlam]
                                    · linarith only [h2358, h2411, hlam]
                                  · linarith only [h0, h2410, hlam, p2363_1]
                                · linarith only [h2409, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h2186, h2358, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2363_1]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                rcases p2363_3 (m.d 0 2) (by simp) with h2418 | h2418
                                · linarith only [h0, h2418, hlam]
                                · linarith only [h2186, h2418, hlam]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                rcases p2363_3 (m.d 0 2) (by simp) with h2421 | h2421
                                · linarith only [h0, h2421, hlam]
                                · linarith only [h2187, h2421, hlam]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                rcases p2363_3 (m.d 0 2) (by simp) with h2424 | h2424
                                · linarith only [h0, h2424, hlam]
                                · linarith only [h2188, h2424, hlam]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h2186, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h2351, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                rcases p2363_3 (m.d 0 2) (by simp) with h2430 | h2430
                                · rcases p2363_3 (m.d 1 2) (by simp) with h2431 | h2431
                                  · rcases p2363_3 (m.d 2 3) (by simp) with h2432 | h2432
                                    · rcases p2363_3 (m.d 2 4) (by simp) with h2433 | h2433
                                      · linarith only [h2357, h2433, hlam]
                                      · rcases p2363_3 (m.d 2 5) (by simp) with h2435 | h2435
                                        · linarith only [h2358, h2435, hlam]
                                        · linarith only [h2359, h2435, hlam]
                                    · linarith only [h2357, h2432, hlam]
                                  · linarith only [h2352, h2431, hlam]
                                · linarith only [h2187, h2430, hlam]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                rcases p2363_3 (m.d 0 2) (by simp) with h2441 | h2441
                                · rcases p2363_3 (m.d 1 2) (by simp) with h2442 | h2442
                                  · rcases p2363_3 (m.d 2 3) (by simp) with h2443 | h2443
                                    · rcases p2363_3 (m.d 2 4) (by simp) with h2444 | h2444
                                      · linarith only [h2357, h2444, hlam]
                                      · rcases p2363_3 (m.d 2 5) (by simp) with h2446 | h2446
                                        · linarith only [h2358, h2446, hlam]
                                        · rcases h4bigk with h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c | h2448c
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2190, h2352, h2357, hc34, hlam, hphi, p2448_1, u4elo4]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2190, h2357, hc34, hlam, hphi, p2448_1, u4elo4]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2190, hc34, hlam, hphi, p2448_1, u4elo4]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2190, hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2185, hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2357, hc34, hlam, hphi, p2448_1, u4elo1]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2185, h2190, hc34, hlam, hphi, p2448_1, u4elo4]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2355, hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2187, hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2352, hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2448_1, u4elo2]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2359, hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2189, hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2353, hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2357, hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2361, hlam, p2448_0]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2448_1, u4elo4]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2352, hc24, hlam, hphi, p2448_1, u4elo4]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [h2357, hc34, hlam, hphi, p2448_1, u4elo4]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2448_1, u4elo4]
                                          · have p2448_0 := h2448c.1
                                            have p2448_1 := h2448c.2.1
                                            have p2448_2 := h2448c.2.2.1
                                            have p2448_3 := h2448c.2.2.2
                                            linarith only [hlam, p2448_0]
                                    · linarith only [h2358, h2443, hlam]
                                  · linarith only [h0, h2186, h2442, hlam, p2363_1]
                                · linarith only [h2188, h2441, hlam]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h2187, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h2352, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h2357, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h2359, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h2188, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h1695, h2351, hc01, hc25, hlam, hphi, ht12, p2363_1]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h2358, hlam, p2363_0]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [h2188, h2190, h2357, hc34, hlam, hphi, p2363_1, u4elo4]
                              · have p2363_0 := h2363c.1
                                have p2363_1 := h2363c.2.1
                                have p2363_2 := h2363c.2.2.1
                                have p2363_3 := h2363c.2.2.2
                                linarith only [hlam, p2363_0]
                        · linarith only [h2354, h2355, h2357, h2358, hc34, hlam, hphi, u4elo4]
                      · linarith only [h2189, h2190, h2357, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2489 | h2489
                    · linarith only [h1695, h2185, h2190, h2354, h2489, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1695, h2185, h2354, h2489, hc14, hlam, hphi, u4elo4]
                · linarith only [h1695, h2185, h2352, h2353, hc24, hlam, hphi, u4elo3]
              · linarith only [h1695, h2351, h2352, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h2185, h2186, h2351, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1695, h2185, h2189, hc14, hlam, hphi, u4elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2496 | h2496
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2497 | h2497
          · linarith only [h0, h2185, h2188, h2497, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2499 | h2499
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2500 | h2500
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2501 | h2501
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2502 | h2502
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2503 | h2503
                    · linarith only [h1695, h2185, h2497, h2503, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2505 | h2505
                      · linarith only [h2186, h2188, h2497, h2505, hc34, hlam, hphi, u4elo4]
                      · linarith only [h2186, h2188, h2496, h2497, h2505, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2508 | h2508
                    · linarith only [h1695, h2185, h2188, h2497, h2502, h2508, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h1695, h2185, h2502, h2508, hc14, hlam, hphi, u4elo4]
                · linarith only [h1695, h2185, h2500, h2501, hc24, hlam, hphi, u4elo3]
              · linarith only [h0, h2185, h2500, hc14, hlam, hphi, u4elo2]
            · linarith only [h0, h2185, h2186, h2499, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1695, h2185, h2496, hc14, hlam, hphi, u4elo3]
    · linarith only [h0, h2185, h2187, hc14, hlam, hphi, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2516 | h2516
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2517 | h2517
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2518 | h2518
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2519 | h2519
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2520 | h2520
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2521 | h2521
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2522 | h2522
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2523 | h2523
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2524 | h2524
                    · linarith only [h0, h2185, h2186, h2520, h2524, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h2519, h2522, h2524, hc34, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2527 | h2527
                    · linarith only [h0, h2185, h2186, h2520, h2523, h2527, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h2185, h2186, h2519, h2520, h2523, h2527, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h2186, h2520, h2522, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h2185, h2521, hc14, hlam, hphi, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2532 | h2532
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2533 | h2533
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2534 | h2534
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2535 | h2535
                    · linarith only [h0, h2185, h2520, h2535, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h2519, h2533, h2535, hc34, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2538 | h2538
                    · linarith only [h0, h2185, h2520, h2534, h2538, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h2185, h2519, h2520, h2534, h2538, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h2520, h2533, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h2185, h2532, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2543 | h2543
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2544 | h2544
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2545 | h2545
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2546 | h2546
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2547 | h2547
                    · linarith only [h0, h2185, h2186, h2519, h2543, h2547, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2549 | h2549
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2550 | h2550
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2551 | h2551
                          · linarith only [h2185, h2519, h2544, h2551, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2553 | h2553
                            · linarith only [h2185, h2519, h2544, h2549, h2553, hlam]
                            · rcases h2bigk with h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c | h2555c
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h0, hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2186, hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2186, h2543, h2549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2555_1]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2186, h2543, h2549, h2551, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2555_1]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                rcases p2555_3 (m.d 0 2) (by simp) with h2561 | h2561
                                · linarith only [h0, h2561, hlam]
                                · rcases p2555_3 (m.d 1 2) (by simp) with h2563 | h2563
                                  · rcases p2555_3 (m.d 2 3) (by simp) with h2564 | h2564
                                    · linarith only [h2543, h2564, hlam]
                                    · linarith only [h2186, h2564, hlam]
                                  · linarith only [h0, h2563, hlam]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h0, h2186, hc01, hc12, hlam, hphi, p2555_1]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h0, h2185, h2186, h2543, h2544, hlam, p2555_2]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2186, h2517, h2543, hlam, p2555_2]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h0, h2185, h2543, h2544, h2549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2555_1]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2543, hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                rcases p2555_3 (m.d 0 2) (by simp) with h2575 | h2575
                                · linarith only [h2186, h2575, hlam]
                                · linarith only [h2516, h2575, hlam]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                rcases p2555_3 (m.d 0 2) (by simp) with h2578 | h2578
                                · linarith only [h2186, h2578, hlam]
                                · linarith only [h2517, h2578, hlam]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2516, hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2544, hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2549, hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2551, hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2517, hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2517, h2543, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2555_1]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2550, hlam, p2555_0]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [h2186, h2517, h2543, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2555_1]
                              · have p2555_0 := h2555c.1
                                have p2555_1 := h2555c.2.1
                                have p2555_2 := h2555c.2.2.1
                                have p2555_3 := h2555c.2.2.2
                                linarith only [hlam, p2555_0]
                        · linarith only [h0, h2186, h2543, h2546, h2550, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2185, h2186, h2544, h2549, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2593 | h2593
                    · linarith only [h2185, h2519, h2593, hlam]
                    · linarith only [h0, h2185, h2186, h2543, h2544, h2546, h2593, hc24, hlam, hphi, u4elo4]
                · linarith only [h0, h2185, h2186, h2543, h2544, h2545, hc24, hlam, hphi, u4elo3]
              · linarith only [h0, h2544, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2598 | h2598
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2599 | h2599
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2600 | h2600
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2601 | h2601
                    · linarith only [h0, h2185, h2543, h2601, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2603 | h2603
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2604 | h2604
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2605 | h2605
                          · linarith only [h2185, h2519, h2598, h2605, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2607 | h2607
                            · linarith only [h2519, h2607, hc04, hlam, hphi, u4elo3]
                            · rcases h2bigk with h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c | h2609c
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h0, hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h2186, hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                rcases p2609_3 (m.d 0 2) (by simp) with h2613 | h2613
                                · rcases p2609_3 (m.d 1 2) (by simp) with h2614 | h2614
                                  · rcases p2609_3 (m.d 2 3) (by simp) with h2615 | h2615
                                    · rcases p2609_3 (m.d 2 4) (by simp) with h2616 | h2616
                                      · linarith only [h2616, hlam, p2609_0]
                                      · rcases p2609_3 (m.d 2 5) (by simp) with h2618 | h2618
                                        · linarith only [h2517, h2618, hlam]
                                        · linarith only [h2605, h2618, hlam]
                                    · linarith only [h2603, h2615, hlam]
                                  · linarith only [h2598, h2614, hlam]
                                · linarith only [h2613, hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                rcases p2609_3 (m.d 0 2) (by simp) with h2624 | h2624
                                · rcases p2609_3 (m.d 1 2) (by simp) with h2625 | h2625
                                  · rcases p2609_3 (m.d 2 3) (by simp) with h2626 | h2626
                                    · rcases p2609_3 (m.d 2 4) (by simp) with h2627 | h2627
                                      · linarith only [h2516, h2627, hlam]
                                      · rcases p2609_3 (m.d 2 5) (by simp) with h2629 | h2629
                                        · linarith only [h2629, hlam, p2609_0]
                                        · rcases h4bigk with h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2519, h2598, h2603, hc34, hlam, hphi, p2631_1, u4elo4]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2519, h2603, hc34, hlam, hphi, p2631_1, u4elo4]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2519, hc34, hlam, hphi, p2631_1, u4elo4]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2519, hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2185, hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2603, hc34, hlam, hphi, p2631_1, u4elo1]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h0, h2185, h2543, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2631_1]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2601, hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2516, hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2598, hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h0, h2543, h2605, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2609_1, p2631_1]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2605, hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2518, hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2599, hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2603, hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2607, hlam, p2631_0]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2631_1, u4elo4]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2598, hc24, hlam, hphi, p2631_1, u4elo4]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [h2603, hc34, hlam, hphi, p2631_1, u4elo4]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [hc34, hlam, hphi, p2631_1, u4elo4]
                                          · have p2631_0 := h2631c.1
                                            have p2631_1 := h2631c.2.1
                                            have p2631_2 := h2631c.2.2.1
                                            have p2631_3 := h2631c.2.2.2
                                            linarith only [hlam, p2631_0]
                                    · linarith only [h2604, h2626, hlam]
                                  · linarith only [h0, h2625, hlam, p2609_1]
                                · linarith only [h2624, hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h2543, hc02, hc23, hlam, hphi, p2609_1]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h2543, hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                rcases p2609_3 (m.d 0 2) (by simp) with h2663 | h2663
                                · linarith only [h0, h2663, hlam]
                                · linarith only [h2516, h2663, hlam]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                rcases p2609_3 (m.d 0 2) (by simp) with h2666 | h2666
                                · linarith only [h0, h2666, hlam]
                                · linarith only [h2517, h2666, hlam]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                rcases p2609_3 (m.d 0 2) (by simp) with h2669 | h2669
                                · linarith only [h2669, hlam, p2609_0]
                                · rcases p2609_3 (m.d 1 2) (by simp) with h2671 | h2671
                                  · linarith only [h2543, h2671, hlam]
                                  · linarith only [h0, h2671, hlam]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h0, h2185, h2598, h2603, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2609_1]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h0, h2185, h2543, h2598, hlam, p2609_2]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                rcases p2609_3 (m.d 0 2) (by simp) with h2677 | h2677
                                · linarith only [h2186, h2677, hlam]
                                · linarith only [h2517, h2677, hlam]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h2516, hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h2598, hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h2603, hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h2605, hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h2517, hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h0, h2185, h2598, h2603, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2609_1]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h2604, hlam, p2609_0]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [h0, h2517, h2543, h2603, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2609_1]
                              · have p2609_0 := h2609c.1
                                have p2609_1 := h2609c.2.1
                                have p2609_2 := h2609c.2.2.1
                                have p2609_3 := h2609c.2.2.2
                                linarith only [hlam, p2609_0]
                        · linarith only [h0, h2185, h2543, h2598, h2603, h2604, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h2543, h2603, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2692 | h2692
                    · linarith only [h1695, h2185, h2600, h2692, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h2185, h2543, h2600, h2692, hc14, hlam, hphi, u4elo4]
                · linarith only [h0, h2185, h2543, h2598, h2599, hc24, hlam, hphi, u4elo3]
              · linarith only [h0, h2598, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h0, h2185, h2186, h2518, hc14, hlam, hphi, u4elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2698 | h2698
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2699 | h2699
          · linarith only [h0, h2185, h2517, h2699, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2701 | h2701
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2702 | h2702
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2703 | h2703
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2704 | h2704
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2705 | h2705
                    · linarith only [h0, h2185, h2186, h2699, h2701, h2705, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2707 | h2707
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2708 | h2708
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2709 | h2709
                          · linarith only [h0, h2185, h2517, h2701, h2702, h2705, h2708, h2709, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h2185, h2517, h2709, hc14, hlam, hphi, u4elo4]
                        · linarith only [h0, h2185, h2186, h2702, h2704, h2707, h2708, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h2185, h2186, h2702, h2707, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2714 | h2714
                    · linarith only [h1695, h2185, h2704, h2714, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h2185, h2186, h2701, h2704, h2714, hc14, hlam, hphi, u4elo4]
                · linarith only [h0, h2185, h2186, h2701, h2702, h2703, hc24, hlam, hphi, u4elo3]
              · linarith only [h2186, h2516, h2701, h2702, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2719 | h2719
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2720 | h2720
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2721 | h2721
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2722 | h2722
                    · linarith only [h0, h2185, h2699, h2722, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2724 | h2724
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2725 | h2725
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2726 | h2726
                          · linarith only [h0, h2185, h2517, h2699, h2701, h2719, h2726, hc02, hc23, hlam, hphi]
                          · linarith only [h0, h2185, h2517, h2719, h2724, h2726, hc34, hlam, hphi, u4elo4]
                        · linarith only [h0, h2185, h2701, h2719, h2721, h2722, h2724, h2725, hc34, hlam, hphi, u4elo4]
                      · linarith only [h0, h2185, h2701, h2719, h2724, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2731 | h2731
                    · linarith only [h0, h2185, h2517, h2699, h2701, h2721, h2731, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h2185, h2701, h2721, h2731, hc14, hlam, hphi, u4elo4]
                · linarith only [h0, h2185, h2701, h2719, h2720, hc24, hlam, hphi, u4elo3]
              · linarith only [h0, h2185, h2719, hc14, hlam, hphi, u4elo2]
        · linarith only [h0, h2185, h2186, h2698, hc14, hlam, hphi, u4elo3]
    · linarith only [h0, h2185, h2516, hc14, hlam, hphi, u4elo2]

end R2N4
