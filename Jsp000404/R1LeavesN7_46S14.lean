import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_46S12
import Jsp000404.R1LeavesN7_46S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1694 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2201 | h2201
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2202 | h2202
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2203 | h2203
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2204 | h2204
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2205 | h2205
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2206 | h2206
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2207 | h2207
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2208 | h2208
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2209 | h2209
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2210 | h2210
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2211 | h2211
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2212 | h2212
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2213 | h2213
                          · linarith only [h0, h2201, h2213, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h1694, h2201, h2208, h2209, h2210, h2213, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h1694, h2203, h2207, h2212, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1694, h2201, h2203, h2206, h2210, h2211, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h2201, h2210, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2201, h2203, h2209, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2220 | h2220
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2221 | h2221
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2222 | h2222
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2223 | h2223
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2224 | h2224
                          · linarith only [h2201, h2208, h2224, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2226 | h2226
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2227 | h2227
                              · linarith only [h1694, h2201, h2205, h2208, h2220, h2221, h2227, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2229 | h2229
                                · linarith only [h2201, h2208, h2221, h2226, h2229, hlam]
                                · rcases h0bigk with h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c | h2231c
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [hlam, p2231_0]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h0, hlam, p2231_1]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h1694, hlam, p2231_0]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h1694, h2201, h2220, h2221, h2226, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2231_1, u2elo1]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h1694, h2202, h2220, h2221, h2224, h2226, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2231_1, u2elo1]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p2231_1, u2elo1]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [hlam, p2231_0]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h0, h1694, hc01, hlam, hphi, ht12, p2231_1, u2elo1]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    rcases p2231_3 (m.d 0 1) (by simp) with h2240 | h2240
                                    · linarith only [h0, h2240, hlam]
                                    · linarith only [h2201, h2240, hlam]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    rcases p2231_3 (m.d 0 1) (by simp) with h2243 | h2243
                                    · linarith only [h0, h2243, hlam]
                                    · linarith only [h2202, h2243, hlam]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h2202, h2221, h2224, h2226, hc34, hlam, hphi, ht0b, ht45, ht5b, p2231_1, u0elo2]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h2203, hlam, p2231_1]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [hlam, p2231_0]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    rcases p2231_3 (m.d 0 1) (by simp) with h2249 | h2249
                                    · linarith only [h1694, h2249, hlam]
                                    · linarith only [h2201, h2249, hlam]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    rcases p2231_3 (m.d 0 1) (by simp) with h2252 | h2252
                                    · linarith only [h1694, h2252, hlam]
                                    · linarith only [h2202, h2252, hlam]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h2201, hlam, p2231_0]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h2204, hlam, p2231_0]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h2206, hlam, p2231_0]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [hlam, p2231_0]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h2208, hlam, p2231_0]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h2202, hlam, p2231_0]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h2205, hlam, p2231_1]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h2207, hlam, p2231_0]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [h0, h2201, h2202, h2221, h2226, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2231_1, u2elo1]
                                  · have p2231_0 := h2231c.1
                                    have p2231_1 := h2231c.2.1
                                    have p2231_2 := h2231c.2.2.1
                                    have p2231_3 := h2231c.2.2.2
                                    linarith only [hlam, p2231_0]
                            · linarith only [h1694, h2201, h2220, h2222, h2226, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h1694, h2207, h2223, hlam]
                      · linarith only [h1694, h2206, h2222, hlam]
                    · linarith only [h1694, h2220, h2221, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2220, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1694, h2202, h2207, hlam]
            · linarith only [h1694, h2201, h2206, hlam]
          · linarith only [h1694, h2202, h2203, h2205, hlam]
        · linarith only [h1694, h2201, h2203, h2204, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2274 | h2274
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2275 | h2275
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2276 | h2276
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2277 | h2277
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2278 | h2278
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2279 | h2279
                  · linarith only [h2203, h2274, h2279, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2201, h2279, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2282 | h2282
                  · linarith only [h0, h2201, h2203, h2282, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2201, h2282, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h0, h2202, h2203, h2277, hlam]
            · linarith only [h0, h2201, h2203, h2276, hlam]
          · linarith only [h0, h2202, h2275, hlam]
        · linarith only [h0, h2201, h2274, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2289 | h2289
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2290 | h2290
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2291 | h2291
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2292 | h2292
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2293 | h2293
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2294 | h2294
                · linarith only [h2201, h2202, h2294, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2296 | h2296
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2297 | h2297
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2298 | h2298
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2299 | h2299
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2300 | h2300
                          · linarith only [h2201, h2294, h2300, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2302 | h2302
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2303 | h2303
                              · linarith only [h2201, h2202, h2297, h2300, h2303, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2305 | h2305
                                · linarith only [h2201, h2202, h2297, h2300, h2302, h2305, hlam]
                                · rcases h0bigk with h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c | h2307c
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [hlam, p2307_0]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h0, hlam, p2307_1]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h1694, hlam, p2307_0]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h2202, h2296, h2299, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2307_1, u2elo1]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h2202, hlam, p2307_1]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p2307_1, u2elo1]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [hlam, p2307_0]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h0, h2293, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2307_1, u2elo1]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    rcases p2307_3 (m.d 0 1) (by simp) with h2316 | h2316
                                    · linarith only [h0, h2316, hlam]
                                    · linarith only [h2201, h2316, hlam]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h0, h2201, h2202, h2297, h2302, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2307_1, u2elo1]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h2201, h2297, h2302, hc34, hlam, hphi, ht0b, ht45, ht5b, p2307_1, u0elo2]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h2289, hlam, p2307_1]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [hlam, p2307_0]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    rcases p2307_3 (m.d 0 1) (by simp) with h2323 | h2323
                                    · linarith only [h1694, h2323, hlam]
                                    · linarith only [h2201, h2323, hlam]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h1694, h2201, h2202, h2296, h2297, h2302, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2307_1, u2elo1]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h2201, hlam, p2307_0]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h2290, hlam, p2307_0]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h2292, hlam, p2307_0]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [hlam, p2307_0]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h2294, hlam, p2307_0]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h2201, h2297, h2302, hc34, hlam, hphi, ht0b, ht45, ht5b, p2307_1, u0elo4]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h2291, hlam, p2307_1]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [h2293, hlam, p2307_0]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    rcases p2307_3 (m.d 0 1) (by simp) with h2335 | h2335
                                    · linarith only [h2202, h2335, hlam]
                                    · linarith only [h2201, h2335, hlam]
                                  · have p2307_0 := h2307c.1
                                    have p2307_1 := h2307c.2.1
                                    have p2307_2 := h2307c.2.2.1
                                    have p2307_3 := h2307c.2.2.2
                                    linarith only [hlam, p2307_0]
                            · linarith only [h2201, h2202, h2296, h2298, h2299, h2302, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h1694, h2293, h2299, hlam]
                      · linarith only [h1694, h2292, h2298, hlam]
                    · linarith only [h0, h2201, h2297, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2201, h2296, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2344 | h2344
                · linarith only [h1694, h2201, h2293, h2344, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2346 | h2346
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2347 | h2347
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2348 | h2348
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2349 | h2349
                        · linarith only [h1694, h2201, h2293, h2346, h2347, h2349, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2351 | h2351
                          · linarith only [h2201, h2344, h2351, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2353 | h2353
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2354 | h2354
                              · linarith only [h1694, h2349, h2351, h2354, hc01, hlam, hphi, ht12, u2elo3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2356 | h2356
                                · linarith only [h1694, h2201, h2347, h2349, h2351, h2353, h2356, hlam]
                                · linarith only [h1694, h2201, h2347, h2349, h2353, h2356, hc34, hc45, hlam, hphi]
                            · linarith only [h1694, h2292, h2349, h2353, hc23, hc35, hlam, hphi]
                      · linarith only [h1694, h2201, h2292, h2348, hlam]
                    · linarith only [h0, h2347, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2289, h2346, hlam]
            · linarith only [h1694, h2201, h2292, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2364 | h2364
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2365 | h2365
              · linarith only [h2289, h2291, h2365, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2367 | h2367
                · linarith only [h1694, h2201, h2289, h2291, h2367, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2369 | h2369
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2370 | h2370
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2371 | h2371
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2372 | h2372
                        · linarith only [h1694, h2201, h2365, h2369, h2370, h2372, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2374 | h2374
                          · linarith only [h2201, h2367, h2374, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2376 | h2376
                            · linarith only [h2289, h2291, h2376, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                            · linarith only [h2289, h2291, h2364, h2376, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h1694, h2201, h2364, h2371, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h2201, h2370, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2201, h2369, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h1694, h2201, h2364, hlam]
        · linarith only [h0, h2201, h2290, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2384 | h2384
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2385 | h2385
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2386 | h2386
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2387 | h2387
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2388 | h2388
                · linarith only [h2201, h2202, h2388, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2390 | h2390
                  · linarith only [h2289, h2384, h2390, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2201, h2390, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h2289, h2385, h2387, hlam]
            · linarith only [h2201, h2202, h2289, h2385, h2386, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2395 | h2395
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2396 | h2396
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2397 | h2397
                · linarith only [h0, h2201, h2385, h2397, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2399 | h2399
                  · linarith only [h0, h2201, h2289, h2399, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2201, h2399, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2402 | h2402
                · linarith only [h1694, h2201, h2396, h2402, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2404 | h2404
                  · linarith only [h0, h2289, h2404, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2201, h2404, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h2201, h2289, h2395, hlam]
        · linarith only [h0, h2201, h2384, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2409 | h2409
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2410 | h2410
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2411 | h2411
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2412 | h2412
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2413 | h2413
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2414 | h2414
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2415 | h2415
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2416 | h2416
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2417 | h2417
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2418 | h2418
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2419 | h2419
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2420 | h2420
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2421 | h2421
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2422 | h2422
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2423 | h2423
                                · linarith only [h2410, h2421, h2423, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                · linarith only [h2201, h2409, h2416, h2418, h2420, h2423, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h2201, h2409, h2416, h2418, h2420, h2422, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2427 | h2427
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2428 | h2428
                                · rcases h0bigk with h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c | h2429c
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [hlam, p2429_0]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h0, hlam, p2429_1]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h1694, hlam, p2429_0]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h2201, hlam, p2429_1]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h2201, h2416, h2418, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2429_1, u2elo1]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p2429_1, u2elo1]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [hlam, p2429_0]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h0, h2413, h2421, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2429_1, u2elo1]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h0, h2201, h2409, h2419, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2429_1, u2elo1]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    rcases p2429_3 (m.d 0 1) (by simp) with h2439 | h2439
                                    · linarith only [h0, h2439, hlam]
                                    · linarith only [h2409, h2439, hlam]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h2409, h2419, h2428, hc45, hlam, hphi, ht0b, ht5b, p2429_1, u0elo2]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h2410, hlam, p2429_1]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [hlam, p2429_0]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h1694, h2413, h2416, h2421, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2429_1, u2elo1]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    rcases p2429_3 (m.d 0 1) (by simp) with h2446 | h2446
                                    · linarith only [h1694, h2446, hlam]
                                    · linarith only [h2409, h2446, hlam]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h2409, h2419, h2428, hc45, hlam, hphi, ht0b, ht5b, p2429_1, u0elo3]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h2411, hlam, p2429_0]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h2413, hlam, p2429_0]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [hlam, p2429_0]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    rcases p2429_3 (m.d 0 1) (by simp) with h2453 | h2453
                                    · linarith only [h2201, h2453, hlam]
                                    · linarith only [h2409, h2453, hlam]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h2409, hlam, p2429_0]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h2412, hlam, p2429_1]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h2414, hlam, p2429_0]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [h2415, hlam, p2429_1]
                                  · have p2429_0 := h2429c.1
                                    have p2429_1 := h2429c.2.1
                                    have p2429_2 := h2429c.2.2.1
                                    have p2429_3 := h2429c.2.2.2
                                    linarith only [hlam, p2429_0]
                                · linarith only [h2421, h2427, h2428, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                              · linarith only [h0, h2409, h2420, h2427, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h2201, h2415, h2420, hlam]
                        · linarith only [h1694, h2414, h2419, hlam]
                      · linarith only [h1694, h2413, h2418, hlam]
                    · linarith only [h0, h2409, h2417, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h2409, h2416, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h2201, h2409, h2415, hlam]
              · linarith only [h2201, h2409, h2413, h2414, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2470 | h2470
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2471 | h2471
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2472 | h2472
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2473 | h2473
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2474 | h2474
                      · linarith only [h2413, h2470, h2472, h2474, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2476 | h2476
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2477 | h2477
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2478 | h2478
                            · linarith only [h2410, h2413, h2478, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2480 | h2480
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2481 | h2481
                                · rcases h0bigk with h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [hlam, p2482_0]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h0, hlam, p2482_1]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h1694, hlam, p2482_0]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h2201, hlam, p2482_1]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h1694, h2473, h2474, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2482_1, u2elo1]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h2409, hc15, hlam, hphi, ht0b, ht5b, p2482_1, u0elo1]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [hlam, p2482_0]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h0, h1694, h2409, h2476, h2481, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2482_1, u2elo1]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h0, h2201, h2409, h2476, h2481, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2482_1, u2elo1]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    rcases p2482_3 (m.d 0 1) (by simp) with h2492 | h2492
                                    · linarith only [h0, h2492, hlam]
                                    · linarith only [h2409, h2492, hlam]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h2409, h2476, h2481, hc45, hlam, hphi, ht0b, ht5b, p2482_1, u0elo2]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h2410, hlam, p2482_1]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [hlam, p2482_0]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h2413, hlam, p2482_1]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    rcases p2482_3 (m.d 0 1) (by simp) with h2499 | h2499
                                    · linarith only [h1694, h2499, hlam]
                                    · linarith only [h2409, h2499, hlam]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h2409, h2476, h2481, hc45, hlam, hphi, ht0b, ht5b, p2482_1, u0elo3]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h2411, hlam, p2482_0]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h0, h1694, h2409, h2411, h2476, h2481, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2482_1, u2elo1]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [hlam, p2482_0]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    rcases p2482_3 (m.d 0 1) (by simp) with h2506 | h2506
                                    · linarith only [h2201, h2506, hlam]
                                    · linarith only [h2409, h2506, hlam]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h2409, hlam, p2482_0]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h2412, hlam, p2482_1]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h2470, hlam, p2482_0]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [h2471, hlam, p2482_1]
                                  · have p2482_0 := h2482c.1
                                    have p2482_1 := h2482c.2.1
                                    have p2482_2 := h2482c.2.2.1
                                    have p2482_3 := h2482c.2.2.2
                                    linarith only [hlam, p2482_0]
                                · linarith only [h1694, h2409, h2474, h2480, h2481, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                              · linarith only [h1694, h2409, h2474, h2477, h2480, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1694, h2409, h2471, h2474, h2477, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h1694, h2409, h2470, h2476, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h0, h2409, h2473, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h2410, h2472, hlam]
                · linarith only [h1694, h2409, h2413, h2471, hlam]
              · linarith only [h1694, h2409, h2470, hlam]
          · linarith only [h0, h2409, h2412, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2523 | h2523
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2524 | h2524
            · linarith only [h2410, h2411, h2524, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2526 | h2526
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2527 | h2527
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2528 | h2528
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2529 | h2529
                    · linarith only [h1694, h2410, h2411, h2529, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h2409, h2529, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h2409, h2528, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h1694, h2409, h2410, h2411, h2527, hlam]
              · linarith only [h1694, h2409, h2526, hlam]
          · linarith only [h1694, h2409, h2410, h2523, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2536 | h2536
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2537 | h2537
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2538 | h2538
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2539 | h2539
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2540 | h2540
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2541 | h2541
                  · linarith only [h2410, h2541, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2409, h2541, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h2201, h2409, h2540, hlam]
              · linarith only [h2201, h2409, h2410, h2536, h2539, hlam]
            · linarith only [h2410, h2536, h2538, hlam]
          · linarith only [h2201, h2409, h2536, h2537, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2548 | h2548
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2549 | h2549
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2550 | h2550
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2551 | h2551
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2552 | h2552
                  · linarith only [h2410, h2552, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2409, h2552, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h0, h2409, h2536, h2551, hlam]
              · linarith only [h0, h2409, h2536, h2549, h2550, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2557 | h2557
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2558 | h2558
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2559 | h2559
                  · linarith only [h0, h2409, h2410, h2559, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h2409, h2559, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h1694, h2409, h2549, h2558, hlam]
              · linarith only [h0, h2409, h2410, h2557, hlam]
          · linarith only [h0, h2409, h2548, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2565 | h2565
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2566 | h2566
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2567 | h2567
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2568 | h2568
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2569 | h2569
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2570 | h2570
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2571 | h2571
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2572 | h2572
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2573 | h2573
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2574 | h2574
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2575 | h2575
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2576 | h2576
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2577 | h2577
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2578 | h2578
                                · linarith only [h2565, h2576, h2578, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                · linarith only [h0, h2565, h2576, h2577, h2578, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2581 | h2581
                                · linarith only [h2576, h2577, h2581, hlam]
                                · rcases h0bigk with h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c | h2583c
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [hlam, p2583_0]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h0, hlam, p2583_1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h1694, hlam, p2583_0]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h2201, hlam, p2583_1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h2409, hlam, p2583_1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p2583_1, u2elo1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [hlam, p2583_0]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h0, h2568, h2570, h2576, h2577, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2583_1, u2elo1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h0, h2570, h2576, h2577, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2583_1, u2elo1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h0, h2409, hc01, hlam, hphi, ht12, p2583_1, u2elo1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h1694, h2571, hc01, hlam, hphi, ht12, p2583_1, u2elo1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h2565, hlam, p2583_1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [hlam, p2583_0]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h1694, h2570, h2571, h2576, h2577, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2583_1, u2elo1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h1694, h2409, h2571, hc01, hlam, hphi, ht12, p2583_1, u2elo1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h2201, h2571, h2573, hc01, hlam, hphi, ht12, p2583_1, u2elo1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h2566, hlam, p2583_0]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h2568, hlam, p2583_0]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [hlam, p2583_0]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h2201, h2409, h2571, h2573, hc01, hlam, hphi, ht12, p2583_1, u2elo1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h2409, h2571, h2573, h2575, hc01, hlam, hphi, ht12, p2583_1, u2elo1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h2567, hlam, p2583_1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h2569, hlam, p2583_0]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [h2570, hlam, p2583_1]
                                  · have p2583_0 := h2583c.1
                                    have p2583_1 := h2583c.2.1
                                    have p2583_2 := h2583c.2.2.1
                                    have p2583_3 := h2583c.2.2.2
                                    linarith only [hlam, p2583_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2609 | h2609
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2610 | h2610
                                · rcases h0bigk with h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c | h2611c
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [hlam, p2611_0]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h0, hlam, p2611_1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h1694, hlam, p2611_0]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h2201, hlam, p2611_1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h2409, hlam, p2611_1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p2611_1, u2elo1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [hlam, p2611_0]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h0, h2568, h2576, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2611_1, u2elo1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h0, h2201, hc01, hlam, hphi, ht12, p2611_1, u2elo1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h0, h2409, hc01, hlam, hphi, ht12, p2611_1, u2elo1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h1694, h2571, hc01, hlam, hphi, ht12, p2611_1, u2elo1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h2565, hlam, p2611_1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [hlam, p2611_0]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h1694, h2566, h2571, h2609, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2611_1, u2elo1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h1694, h2409, h2571, hc01, hlam, hphi, ht12, p2611_1, u2elo1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h2201, h2571, h2573, hc01, hlam, hphi, ht12, p2611_1, u2elo1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h2566, hlam, p2611_0]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h2568, hlam, p2611_0]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [hlam, p2611_0]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h2201, h2409, h2571, h2573, hc01, hlam, hphi, ht12, p2611_1, u2elo1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h2409, h2571, h2573, h2575, hc01, hlam, hphi, ht12, p2611_1, u2elo1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h2567, hlam, p2611_1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h2569, hlam, p2611_0]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [h2570, hlam, p2611_1]
                                  · have p2611_0 := h2611c.1
                                    have p2611_1 := h2611c.2.1
                                    have p2611_2 := h2611c.2.2.1
                                    have p2611_3 := h2611c.2.2.2
                                    linarith only [hlam, p2611_0]
                                · linarith only [h2576, h2609, h2610, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2638 | h2638
                                · linarith only [h1694, h2568, h2571, h2609, h2638, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · linarith only [h2201, h2570, h2571, h2573, h2576, h2638, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h2201, h2570, h2575, hlam]
                        · linarith only [h1694, h2569, h2574, hlam]
                      · linarith only [h1694, h2568, h2573, hlam]
                    · linarith only [h0, h2572, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2571, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2646 | h2646
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2647 | h2647
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2648 | h2648
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2649 | h2649
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2650 | h2650
                          · linarith only [h2201, h2570, h2646, h2648, h2650, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2652 | h2652
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2653 | h2653
                              · linarith only [h2201, h2566, h2650, h2653, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2655 | h2655
                                · linarith only [h0, h2201, h2565, h2650, h2652, h2655, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases h0bigk with h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c | h2657c
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [hlam, p2657_0]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h0, hlam, p2657_1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h1694, hlam, p2657_0]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h2201, hlam, p2657_1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h2409, hlam, p2657_1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p2657_1, u2elo1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [hlam, p2657_0]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h0, h2569, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2657_1, u2elo1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h0, h2201, hc01, hlam, hphi, ht12, p2657_1, u2elo1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h0, h2409, hc01, hlam, hphi, ht12, p2657_1, u2elo1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h1694, h2646, hc01, hlam, hphi, ht12, p2657_1, u2elo1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h2565, hlam, p2657_1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [hlam, p2657_0]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h1694, h2201, h2646, hc01, hlam, hphi, ht12, p2657_1, u2elo1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h1694, h2409, h2646, hc01, hlam, hphi, ht12, p2657_1, u2elo1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h2201, h2650, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2657_1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h2566, hlam, p2657_0]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h2568, hlam, p2657_0]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [hlam, p2657_0]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h2570, hlam, p2657_0]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h2409, h2646, h2649, hc01, hlam, hphi, ht12, p2657_1, u2elo1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h2567, hlam, p2657_1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h2569, hlam, p2657_0]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [h2201, h2409, h2646, h2649, hc01, hlam, hphi, ht12, p2657_1, u2elo1]
                                  · have p2657_0 := h2657c.1
                                    have p2657_1 := h2657c.2.1
                                    have p2657_2 := h2657c.2.2.1
                                    have p2657_3 := h2657c.2.2.2
                                    linarith only [hlam, p2657_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2683 | h2683
                              · linarith only [h2201, h2568, h2650, h2652, h2683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2685 | h2685
                                · linarith only [h1694, h2201, h2568, h2646, h2650, h2685, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases h0bigk with h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h0, hlam, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h1694, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2201, hlam, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2409, hlam, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p2687_1, u2elo1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h0, h2569, h2652, h2685, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2687_1, u2elo1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h0, h2568, h2652, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2687_1, u2elo1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h0, h2409, hc01, hlam, hphi, ht12, p2687_1, u2elo1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h1694, h2646, hc01, hlam, hphi, ht12, p2687_1, u2elo1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2565, hlam, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h1694, h2568, h2646, h2652, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2687_1, u2elo1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h1694, h2409, h2646, hc01, hlam, hphi, ht12, p2687_1, u2elo1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2201, h2650, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2566, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2568, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2570, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2409, h2646, h2649, hc01, hlam, hphi, ht12, p2687_1, u2elo1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2567, hlam, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2569, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2201, h2409, h2646, h2649, hc01, hlam, hphi, ht12, p2687_1, u2elo1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [hlam, p2687_0]
                        · linarith only [h1694, h2569, h2649, hlam]
                      · linarith only [h0, h1694, h2566, h2568, h2648, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h2647, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2646, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2717 | h2717
                · linarith only [h2568, h2569, h2717, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2719 | h2719
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2720 | h2720
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2721 | h2721
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2722 | h2722
                        · linarith only [h1694, h2569, h2719, h2722, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2724 | h2724
                          · linarith only [h2201, h2717, h2720, h2724, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2726 | h2726
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2727 | h2727
                              · linarith only [h2201, h2566, h2724, h2727, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2729 | h2729
                                · linarith only [h2565, h2724, h2726, h2729, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                                · rcases h0bigk with h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c | h2731c
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [hlam, p2731_0]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h0, hlam, p2731_1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h1694, hlam, p2731_0]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h2201, hlam, p2731_1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h2409, hlam, p2731_1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p2731_1, u2elo1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [hlam, p2731_0]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h0, h2565, h2726, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2731_1, u2elo1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h0, h2201, hc01, hlam, hphi, ht12, p2731_1, u2elo1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h0, h2565, h2569, h2726, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2731_1, u2elo1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h1694, h2722, hc01, hc35, hlam, hphi, ht12, ht23, p2731_1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h2565, hlam, p2731_1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [hlam, p2731_0]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h1694, h2201, h2722, h2729, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2731_1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h2569, hlam, p2731_1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h0, h2566, hc01, hlam, hphi, ht12, p2731_1, u2elo1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h2566, hlam, p2731_0]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h2568, hlam, p2731_0]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [hlam, p2731_0]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h2717, hlam, p2731_0]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h0, h2567, hc01, hlam, hphi, ht12, p2731_1, u2elo1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h2567, hlam, p2731_1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h0, h1694, h2567, hc01, hlam, hphi, ht12, p2731_1, u2elo1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [h0, h2201, h2567, hc01, hlam, hphi, ht12, p2731_1, u2elo1]
                                  · have p2731_0 := h2731c.1
                                    have p2731_1 := h2731c.2.1
                                    have p2731_2 := h2731c.2.2.1
                                    have p2731_3 := h2731c.2.2.2
                                    linarith only [hlam, p2731_0]
                            · linarith only [h1694, h2568, h2722, h2726, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1694, h2566, h2568, h2721, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h2566, h2720, hlam]
                  · linarith only [h0, h2719, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2761 | h2761
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2762 | h2762
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2763 | h2763
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2764 | h2764
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2765 | h2765
                      · linarith only [h2568, h2761, h2763, h2765, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2767 | h2767
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2768 | h2768
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2769 | h2769
                            · linarith only [h2565, h2765, h2769, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2771 | h2771
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2772 | h2772
                                · rcases h0bigk with h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c | h2773c
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [hlam, p2773_0]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h0, hlam, p2773_1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h1694, hlam, p2773_0]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h2201, hlam, p2773_1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h2409, hlam, p2773_1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, p2773_1, u2elo0]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [hlam, p2773_0]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h0, h2761, h2772, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2773_1, u2elo1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h0, h2568, h2761, h2772, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2773_1, u2elo1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h0, h2409, hc01, hlam, hphi, ht12, p2773_1, u2elo1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h1694, h2765, hc01, hc34, hlam, hphi, ht12, ht23, p2773_1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h2565, hlam, p2773_1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [hlam, p2773_0]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h2568, hlam, p2773_1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h2201, h2409, h2568, h2764, hc01, hlam, hphi, ht12, p2773_1, u2elo1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h2201, h2764, hc01, hlam, hphi, ht12, p2773_1, u2elo1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h2566, hlam, p2773_0]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h1694, h2201, h2764, hc01, hlam, hphi, ht12, p2773_1, u2elo1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [hlam, p2773_0]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h2201, h2409, h2764, hc01, hlam, hphi, ht12, p2773_1, u2elo1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h0, h2567, hc01, hlam, hphi, ht12, p2773_1, u2elo1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h2567, hlam, p2773_1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h2761, hlam, p2773_0]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [h2762, hlam, p2773_1]
                                  · have p2773_0 := h2773c.1
                                    have p2773_1 := h2773c.2.1
                                    have p2773_2 := h2773c.2.2.1
                                    have p2773_3 := h2773c.2.2.2
                                    linarith only [hlam, p2773_0]
                                · linarith only [h0, h2566, h2771, h2772, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2800 | h2800
                                · linarith only [h1694, h2761, h2765, h2769, h2771, h2800, hc23, hc34, hlam, hphi]
                                · linarith only [h1694, h2201, h2762, h2764, h2765, h2800, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h1694, h2201, h2761, h2762, h2765, h2768, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h1694, h2566, h2568, h2761, h2767, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h2764, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2763, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2568, h2761, h2762, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2808 | h2808
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2809 | h2809
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2810 | h2810
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2811 | h2811
                      · linarith only [h1694, h2568, h2809, h2811, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2813 | h2813
                        · linarith only [h1694, h2761, h2811, h2813, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2815 | h2815
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2816 | h2816
                            · linarith only [h2565, h2568, h2816, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2818 | h2818
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2819 | h2819
                                · rcases h0bigk with h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h0, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h1694, hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2201, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2409, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, p2820_1, u2elo0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h0, h1694, hc01, hlam, hphi, ht12, p2820_1, u2elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h0, h1694, h2761, h2808, hc01, hlam, hphi, ht12, p2820_1, u2elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h0, h1694, h2761, hc01, hlam, hphi, ht12, p2820_1, u2elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h1694, h2813, h2819, hc01, hc34, hlam, hphi, ht12, ht23, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2565, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2568, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2761, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2201, h2810, hc01, hlam, hphi, ht12, p2820_1, u2elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2566, hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h1694, h2201, h2810, hc01, hlam, hphi, ht12, p2820_1, u2elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2201, h2409, h2810, hc01, hlam, hphi, ht12, p2820_1, u2elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2409, h2810, h2815, hc01, hlam, hphi, ht12, p2820_1, u2elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2567, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h1694, h2409, h2810, h2815, hc01, hlam, hphi, ht12, p2820_1, u2elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2808, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [hlam, p2820_0]
                                · linarith only [h1694, h2568, h2818, h2819, hc01, hlam, hphi, ht12, u2elo4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2847 | h2847
                                · rcases h0bigk with h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c | h2848c
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [hlam, p2848_0]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h0, hlam, p2848_1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h1694, hlam, p2848_0]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h2201, hlam, p2848_1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h2409, hlam, p2848_1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p2848_1, u2elo1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [hlam, p2848_0]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h0, h1694, hc01, hlam, hphi, ht12, p2848_1, u2elo1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h0, h2808, h2816, h2818, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2848_1, u2elo1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h0, h2409, hc01, hlam, hphi, ht12, p2848_1, u2elo1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h1694, h2813, h2847, hc01, hc34, hlam, hphi, ht12, ht23, p2848_1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h2565, hlam, p2848_1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [hlam, p2848_0]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h2568, hlam, p2848_1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h2761, hlam, p2848_1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h2201, h2810, hc01, hlam, hphi, ht12, p2848_1, u2elo1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h2566, hlam, p2848_0]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h1694, h2201, h2810, hc01, hlam, hphi, ht12, p2848_1, u2elo1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [hlam, p2848_0]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h1694, h2201, h2761, h2810, hc01, hlam, hphi, ht12, p2848_1, u2elo1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h2409, h2810, h2815, hc01, hlam, hphi, ht12, p2848_1, u2elo1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h2567, hlam, p2848_1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h1694, h2409, h2810, h2815, hc01, hlam, hphi, ht12, p2848_1, u2elo1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [h2808, hlam, p2848_1]
                                  · have p2848_0 := h2848c.1
                                    have p2848_1 := h2848c.2.1
                                    have p2848_2 := h2848c.2.2.1
                                    have p2848_3 := h2848c.2.2.2
                                    linarith only [hlam, p2848_0]
                                · linarith only [h1694, h2201, h2568, h2808, h2810, h2847, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h2201, h2808, h2815, hlam]
                    · linarith only [h0, h2810, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2809, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2878 | h2878
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2879 | h2879
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2880 | h2880
                      · linarith only [h1694, h2568, h2878, h2880, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2882 | h2882
                        · linarith only [h1694, h2761, h2879, h2880, h2882, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2884 | h2884
                          · linarith only [h2201, h2808, h2879, h2884, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2886 | h2886
                            · linarith only [h1694, h2565, h2880, h2886, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2888 | h2888
                              · linarith only [h0, h2201, h2566, h2884, h2888, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2890 | h2890
                                · linarith only [h1694, h2880, h2884, h2890, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h1694, h2880, h2890, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h2879, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2565, h2878, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2895 | h2895
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2896 | h2896
              · linarith only [h2565, h2567, h2896, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2898 | h2898
                · linarith only [h2565, h2567, h2895, h2898, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2900 | h2900
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2901 | h2901
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2902 | h2902
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2903 | h2903
                        · linarith only [h2895, h2896, h2900, h2903, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2905 | h2905
                          · linarith only [h2201, h2898, h2901, h2905, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2907 | h2907
                            · linarith only [h2565, h2567, h2907, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                            · linarith only [h1694, h2895, h2903, h2907, hc23, hc35, hlam, hphi]
                      · linarith only [h2565, h2567, h2895, h2902, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h2566, h2567, h2901, hc12, hlam, hphi, u2elo4]
                  · linarith only [h0, h2900, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2913 | h2913
              · linarith only [h2565, h2567, h2913, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2915 | h2915
                · linarith only [h2566, h2567, h2915, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2917 | h2917
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2918 | h2918
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2919 | h2919
                      · linarith only [h1694, h2895, h2917, h2919, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2921 | h2921
                        · linarith only [h1694, h2913, h2918, h2919, h2921, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2923 | h2923
                          · linarith only [h2201, h2915, h2918, h2923, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2925 | h2925
                            · linarith only [h2565, h2567, h2919, h2925, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2927 | h2927
                              · linarith only [h2566, h2567, h2923, h2927, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2929 | h2929
                                · linarith only [h1694, h2919, h2923, h2929, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h1694, h2566, h2567, h2919, h2925, h2929, hc01, hc23, hc45, hlam, hphi, ht12, ht34, u2elo4]
                    · linarith only [h2566, h2567, h2918, hc12, hlam, hphi, u2elo4]
                  · linarith only [h0, h2917, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2934 | h2934
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2935 | h2935
            · linarith only [h2565, h2566, h2935, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2937 | h2937
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2938 | h2938
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2939 | h2939
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2940 | h2940
                    · linarith only [h2566, h2940, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h2940, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2565, h2939, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h2565, h2566, h2937, h2938, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2945 | h2945
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2946 | h2946
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2947 | h2947
                    · linarith only [h2566, h2947, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h2947, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2565, h2946, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h2566, h2934, h2945, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2952 | h2952
            · linarith only [h2565, h2566, h2952, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2954 | h2954
              · linarith only [h2565, h2934, h2954, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2956 | h2956
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2957 | h2957
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2958 | h2958
                    · linarith only [h2566, h2958, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h2958, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2565, h2957, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2962 | h2962
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2963 | h2963
                    · linarith only [h2566, h2963, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h2963, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2565, h2962, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2967 | h2967
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2968 | h2968
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2969 | h2969
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2970 | h2970
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2971 | h2971
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2972 | h2972
                  · linarith only [h2565, h2972, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2972, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2975 | h2975
                  · linarith only [h2565, h2967, h2975, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2975, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2565, h2968, h2970, hlam]
            · linarith only [h2565, h2967, h2969, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2980 | h2980
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2981 | h2981
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2982 | h2982
                · linarith only [h2967, h2968, h2982, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2984 | h2984
                  · linarith only [h2565, h2967, h2984, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2984, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2987 | h2987
                · linarith only [h2565, h2967, h2981, h2987, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2989 | h2989
                  · linarith only [h2565, h2967, h2989, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2989, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h2565, h2967, h2980, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2993 | h2993
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2994 | h2994
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2995 | h2995
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2996 | h2996
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2997 | h2997
                  · linarith only [h2565, h2997, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2997, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2967, h2993, h2996, hlam]
              · linarith only [h2967, h2993, h2994, h2995, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3002 | h3002
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3003 | h3003
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3004 | h3004
                  · linarith only [h2565, h2993, h3004, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h3004, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2565, h2993, h2994, h3003, hlam]
              · linarith only [h2565, h2993, h3002, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3009 | h3009
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3010 | h3010
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3011 | h3011
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3012 | h3012
                  · linarith only [h2565, h3012, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h3012, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3015 | h3015
                  · linarith only [h0, h2565, h3015, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3015, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3018 | h3018
                · linarith only [h3009, h3010, h3018, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3020 | h3020
                  · linarith only [h0, h2565, h3020, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3020, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3023 | h3023
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3024 | h3024
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3025 | h3025
                  · linarith only [h0, h2565, h3025, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3025, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h3009, h3023, h3024, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3029 | h3029
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3030 | h3030
                  · linarith only [h0, h2565, h3030, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3030, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3033 | h3033
                  · linarith only [h0, h2565, h3033, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3033, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1694 | h1694
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x1_x0 m hb0 hb2 hb4 h0 h1694
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x1_x1 m hb0 hb2 hb4 h0 h1694

set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x1 m hb0 hb2 hb4 h0

end R2N4
