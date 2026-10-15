import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_46S7
import Jsp000404.R1LeavesN7_46S8
import Jsp000404.R1LeavesN7_46S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6014000 in
set_option maxHeartbeats 6014000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h966 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1840 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2211 | h2211
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2212 | h2212
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2213 | h2213
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2214 | h2214
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2215 | h2215
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2216 | h2216
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2217 | h2217
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2218 | h2218
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2219 | h2219
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2220 | h2220
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2221 | h2221
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2222 | h2222
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2223 | h2223
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2224 | h2224
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2225 | h2225
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2226 | h2226
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2227 | h2227
                                  · linarith only [h2212, h2224, h2227, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h1840, h2211, h2221, h2223, h2227, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h1840, h2211, h2221, h2223, h2226, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · linarith only [h2216, h2225, hc23, hlam, hphi, u3elo0]
                            · linarith only [h2215, h2224, h966, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1840, h2217, h2223, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h1840, h2211, h2220, h2221, h2222, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                      · linarith only [h2215, h2221, h966, hlam]
                    · linarith only [h0, h2214, h2220, hlam]
                  · linarith only [h0, h2213, h2219, hlam]
                · linarith only [h0, h2218, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h1840, h2211, h2217, hlam]
            · linarith only [h1840, h2211, h2215, h2216, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2241 | h2241
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2242 | h2242
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2243 | h2243
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2244 | h2244
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2245 | h2245
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2246 | h2246
                      · linarith only [h2211, h2215, h2245, h2246, h966, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h2211, h2245, h2246, h966, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h2214, h2243, h2245, h966, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2211, h2213, h2244, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h0, h2211, h2243, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h1840, h2211, h2242, hlam]
            · linarith only [h2211, h2241, h966, hlam]
        · linarith only [h0, h2211, h2214, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2255 | h2255
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2256 | h2256
          · linarith only [h2212, h2213, h2256, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2258 | h2258
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2259 | h2259
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2260 | h2260
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2261 | h2261
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2262 | h2262
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2263 | h2263
                      · linarith only [h2211, h2256, h2262, h2263, h966, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h2211, h2262, h2263, h966, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h2213, h2261, h2262, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2267 | h2267
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2268 | h2268
                      · linarith only [h2211, h2256, h2267, h2268, h966, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h2211, h2267, h2268, h966, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h0, h2255, h2267, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h2212, h2260, hlam]
              · linarith only [h0, h2211, h2213, h2259, hlam]
            · linarith only [h2211, h2258, h966, hlam]
        · linarith only [h2211, h2212, h2255, h966, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2276 | h2276
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2277 | h2277
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2278 | h2278
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2279 | h2279
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2280 | h2280
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2281 | h2281
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2282 | h2282
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2283 | h2283
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2284 | h2284
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2285 | h2285
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2286 | h2286
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2287 | h2287
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2288 | h2288
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2289 | h2289
                                · linarith only [h2212, h2276, h2281, h2289, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                · linarith only [h2212, h2276, h2280, h2281, h2289, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · linarith only [h1840, h2212, h2276, h2288, hc01, hlam, hphi, ht12, ht23, u3elo4]
                            · linarith only [h1840, h2212, h2276, h2287, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · linarith only [h1840, h2211, h2276, h2280, h2283, h2286, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h2212, h2281, h2285, hc02, hlam, hphi, ht23, u3elo4]
                      · linarith only [h2212, h2276, h2278, h2281, h2284, hlam]
                    · linarith only [h2212, h2277, h2283, hc12, hc23, hlam, hphi]
                  · linarith only [h2212, h2276, h2281, h2282, hlam]
                · linarith only [h0, h2211, h2281, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h1840, h2211, h2280, hlam]
            · linarith only [h0, h2211, h2212, h2279, hlam]
          · linarith only [h2212, h2276, h2278, hlam]
        · linarith only [h1840, h2211, h2276, h2277, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2304 | h2304
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2305 | h2305
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2306 | h2306
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2307 | h2307
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2308 | h2308
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2309 | h2309
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2310 | h2310
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2311 | h2311
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2312 | h2312
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2313 | h2313
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2314 | h2314
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2315 | h2315
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2316 | h2316
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2317 | h2317
                                  · rcases h0bigk with h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c | h2318c
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [hlam, p2318_0]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h0, hlam, p2318_1]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h966, hlam, p2318_0]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h1840, hlam, p2318_1]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h0, h2276, h2309, h2311, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2318_1, u3elo1]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2276, h2309, h2311, hc01, hlam, hphi, ht12, ht23, p2318_1, u3elo1]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [hlam, p2318_0]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2212, hlam, p2318_0]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2276, hlam, p2318_1]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2211, h2276, h2309, h2310, h2311, h2315, h2317, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2318_1, u3elo1]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2211, h2310, h2315, h2317, hc45, hlam, hphi, ht0b, ht5b, p2318_1, u0elo2]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2212, h2308, hc02, hlam, hphi, ht23, p2318_1, u3elo1]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [hlam, p2318_0]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h1840, h2211, h2212, h2308, h2310, h2315, h2317, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2318_1, u3elo1]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      rcases p2318_3 (m.d 0 1) (by simp) with h2333 | h2333
                                      · linarith only [h2333, h966, hlam]
                                      · linarith only [h2211, h2333, hlam]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2211, h2310, h2315, h2317, hc45, hlam, hphi, ht0b, ht5b, p2318_1, u0elo3]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h0, h2211, h2276, h2309, h2310, h2311, h2315, h2317, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2318_1, u3elo1]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2305, hlam, p2318_0]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [hlam, p2318_0]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      rcases p2318_3 (m.d 0 1) (by simp) with h2340 | h2340
                                      · linarith only [h1840, h2340, hlam]
                                      · linarith only [h2211, h2340, hlam]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2211, hlam, p2318_0]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2304, hlam, p2318_1]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2306, hlam, p2318_0]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [h2307, hlam, p2318_1]
                                    · have p2318_0 := h2318c.1
                                      have p2318_1 := h2318c.2.1
                                      have p2318_2 := h2318c.2.2.1
                                      have p2318_3 := h2318c.2.2.2
                                      linarith only [hlam, p2318_0]
                                  · linarith only [h2211, h2313, h2317, h966, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h0, h2211, h2276, h2313, h2316, hlam]
                              · linarith only [h0, h2212, h2315, hc01, hlam, hphi, ht12, ht23, u3elo4]
                            · linarith only [h0, h2211, h2212, h2313, h2314, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h1840, h2305, h2307, h2313, h966, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h2211, h2310, h2312, h966, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                      · linarith only [h0, h2211, h2212, h2305, h2308, h2310, h2311, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h2276, h2304, h2310, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2212, h2308, h2309, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2211, h2308, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h1840, h2211, h2307, hlam]
            · linarith only [h0, h2211, h2276, h2305, h2306, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2360 | h2360
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2361 | h2361
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2362 | h2362
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2363 | h2363
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2364 | h2364
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2365 | h2365
                      · linarith only [h2305, h2365, hc03, hlam, hphi, u3elo1]
                      · linarith only [h2365, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h2211, h2212, h2362, h2364, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h2211, h2212, h2362, h2363, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h2211, h2362, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h0, h2211, h2212, h2305, h2361, hlam]
            · linarith only [h0, h2211, h2212, h2360, hlam]
        · linarith only [h0, h2211, h2304, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2374 | h2374
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2375 | h2375
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2376 | h2376
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2377 | h2377
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2378 | h2378
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2379 | h2379
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2380 | h2380
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2381 | h2381
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2382 | h2382
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2383 | h2383
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2384 | h2384
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2385 | h2385
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2386 | h2386
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2387 | h2387
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2388 | h2388
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2389 | h2389
                                  · linarith only [h2374, h2386, h2389, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h2374, h2386, h2388, h2389, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2392 | h2392
                                  · linarith only [h2386, h2388, h2392, hlam]
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
                                      linarith only [h966, hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h1840, hlam, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2211, hlam, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      rcases p2394_3 (m.d 0 1) (by simp) with h2400 | h2400
                                      · linarith only [h0, h2400, hlam]
                                      · rcases p2394_3 (m.d 0 2) (by simp) with h2402 | h2402
                                        · rcases p2394_3 (m.d 0 3) (by simp) with h2403 | h2403
                                          · linarith only [h2374, h2403, hlam]
                                          · linarith only [h2403, h966, hlam]
                                        · linarith only [h0, h2402, hlam]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2377, h2379, h2386, h2388, hc34, hlam, hphi, ht0b, ht45, ht5b, p2394_1, u0elo1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2379, h2386, h2388, hc34, hlam, hphi, ht0b, ht45, ht5b, p2394_1, u0elo1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2379, h2386, h2388, hc34, hlam, hphi, ht0b, ht45, ht5b, p2394_1, u0elo1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, p2394_1, u3elo0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2374, hlam, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2379, h2386, h2388, h966, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2394_1, u3elo1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2211, h966, hc01, hlam, hphi, ht12, ht23, p2394_1, u3elo1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h1840, h2383, hc01, hlam, hphi, ht12, ht23, p2394_1, u3elo1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2375, hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2377, hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h1840, h2211, h2383, hc01, hlam, hphi, ht12, ht23, p2394_1, u3elo1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2211, h2383, h2385, hc01, hlam, hphi, ht12, ht23, p2394_1, u3elo1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2376, hlam, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2378, hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2379, hlam, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [hlam, p2394_0]
                              · linarith only [h2378, h2387, h966, hc23, hlam, hphi, u3elo1]
                            · linarith only [h2377, h2386, h966, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1840, h2379, h2385, hlam]
                        · linarith only [h2378, h2384, h966, hlam]
                      · linarith only [h2377, h2383, h966, hlam]
                    · linarith only [h0, h2376, h2382, hlam]
                  · linarith only [h0, h2375, h2381, hlam]
                · linarith only [h0, h2380, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2434 | h2434
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2435 | h2435
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2436 | h2436
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2437 | h2437
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2438 | h2438
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2439 | h2439
                          · linarith only [h1840, h2379, h2437, h2439, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2441 | h2441
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2442 | h2442
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2443 | h2443
                                · linarith only [h1840, h2375, h2439, h2443, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2445 | h2445
                                  · linarith only [h1840, h2374, h2439, h2441, h2445, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                  · rcases h0bigk with h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h0, hlam, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h966, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h1840, hlam, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2211, hlam, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      rcases p2447_3 (m.d 0 1) (by simp) with h2453 | h2453
                                      · linarith only [h0, h2453, hlam]
                                      · rcases p2447_3 (m.d 0 2) (by simp) with h2455 | h2455
                                        · rcases p2447_3 (m.d 0 3) (by simp) with h2456 | h2456
                                          · linarith only [h2374, h2456, hlam]
                                          · linarith only [h2456, h966, hlam]
                                        · linarith only [h0, h2455, hlam]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2374, h2442, h2445, hc34, hlam, hphi, ht0b, ht45, ht5b, p2447_1, u0elo1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      rcases p2447_3 (m.d 0 1) (by simp) with h2462 | h2462
                                      · linarith only [h0, h2462, hlam]
                                      · rcases p2447_3 (m.d 0 2) (by simp) with h2464 | h2464
                                        · rcases p2447_3 (m.d 0 3) (by simp) with h2465 | h2465
                                          · linarith only [h2374, h2465, hlam]
                                          · linarith only [h2377, h2465, hlam]
                                        · linarith only [h2375, h2464, hlam]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      rcases p2447_3 (m.d 0 1) (by simp) with h2469 | h2469
                                      · linarith only [h0, h2469, hlam]
                                      · rcases p2447_3 (m.d 0 2) (by simp) with h2471 | h2471
                                        · rcases p2447_3 (m.d 0 3) (by simp) with h2472 | h2472
                                          · linarith only [h2374, h2472, hlam]
                                          · linarith only [h2378, h2472, hlam]
                                        · linarith only [h2376, h2471, hlam]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, p2447_1, u3elo0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2374, hlam, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h1840, h966, hc01, hlam, hphi, ht12, ht23, p2447_1, u3elo1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2211, h966, hc01, hlam, hphi, ht12, ht23, p2447_1, u3elo1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h1840, h2439, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2375, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2377, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2379, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2378, h966, hc01, hlam, hphi, ht12, ht23, p2447_1, u3elo1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2376, hlam, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2378, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h1840, h2378, h966, hc01, hlam, hphi, ht12, ht23, p2447_1, u3elo1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [hlam, p2447_0]
                              · linarith only [h2378, h2442, h966, hc23, hlam, hphi, u3elo1]
                            · linarith only [h2377, h2441, h966, hc23, hlam, hphi, u3elo1]
                        · linarith only [h2378, h2438, h966, hlam]
                      · linarith only [h2437, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h2376, h2378, h2436, hc01, hlam, hphi, ht12, ht23, u3elo0]
                  · linarith only [h0, h2375, h2435, hlam]
                · linarith only [h0, h2434, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2498 | h2498
              · linarith only [h2377, h2378, h2498, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2500 | h2500
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2501 | h2501
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2502 | h2502
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2503 | h2503
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2504 | h2504
                        · linarith only [h2378, h2504, hc03, hlam, hphi, u3elo1]
                        · linarith only [h2504, h966, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h2377, h2503, h966, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2376, h2500, h2502, h966, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2375, h2377, h2378, h2501, hc02, hlam, hphi, ht23, u3elo4]
                · linarith only [h0, h2374, h2500, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2511 | h2511
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2512 | h2512
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2513 | h2513
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2514 | h2514
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2515 | h2515
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2516 | h2516
                      · linarith only [h2377, h2516, hc03, hlam, hphi, u3elo1]
                      · linarith only [h2516, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h2376, h2515, hlam]
                  · linarith only [h0, h2375, h2514, hlam]
                · linarith only [h0, h2513, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h2377, h2511, h2512, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2523 | h2523
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2524 | h2524
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2525 | h2525
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2526 | h2526
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2527 | h2527
                      · linarith only [h2377, h2527, hc03, hlam, hphi, u3elo1]
                      · linarith only [h2527, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h2376, h2524, h2526, h966, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2375, h2525, hlam]
                · linarith only [h0, h2524, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2533 | h2533
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2534 | h2534
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2535 | h2535
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2536 | h2536
                      · linarith only [h2377, h2536, h966, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h2536, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h2376, h2535, hlam]
                  · linarith only [h0, h2375, h2534, hlam]
                · linarith only [h0, h2533, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2542 | h2542
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2543 | h2543
            · linarith only [h2374, h2376, h2543, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2545 | h2545
              · linarith only [h2375, h2376, h2545, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2547 | h2547
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2548 | h2548
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2549 | h2549
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2550 | h2550
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2551 | h2551
                        · linarith only [h1840, h2542, h2543, h2551, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h2551, h966, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h2542, h2550, h966, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2555 | h2555
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2556 | h2556
                        · linarith only [h2543, h2556, hc03, hlam, hphi, u3elo1]
                        · linarith only [h2556, h966, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h2542, h2555, h966, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h2375, h2548, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h2374, h2547, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2562 | h2562
            · linarith only [h2374, h2376, h2542, h2562, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2564 | h2564
              · linarith only [h2375, h2376, h2564, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2566 | h2566
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2567 | h2567
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2568 | h2568
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2569 | h2569
                      · linarith only [h2542, h2569, hc03, hlam, hphi, u3elo1]
                      · linarith only [h2569, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2572 | h2572
                      · linarith only [h2542, h2572, h966, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h2572, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2375, h2567, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h2566, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2577 | h2577
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2578 | h2578
          · linarith only [h2374, h2375, h2578, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2580 | h2580
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2581 | h2581
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2582 | h2582
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2583 | h2583
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2584 | h2584
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2585 | h2585
                      · linarith only [h2578, h2585, hc03, hlam, hphi, u3elo1]
                      · linarith only [h2585, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h2375, h2577, h2583, h2584, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2589 | h2589
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2590 | h2590
                      · linarith only [h2578, h2580, h2590, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h2590, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h2577, h2589, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h2582, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h2374, h2375, h2580, h2581, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2596 | h2596
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2597 | h2597
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2598 | h2598
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2599 | h2599
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2600 | h2600
                      · linarith only [h2578, h2600, hc03, hlam, hphi, u3elo1]
                      · linarith only [h2600, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h2375, h2577, h2598, h2599, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2604 | h2604
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2605 | h2605
                      · linarith only [h2578, h2605, h966, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h2605, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h2577, h2604, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h2597, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h2375, h2577, h2596, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2611 | h2611
          · linarith only [h2374, h2375, h2611, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2613 | h2613
            · linarith only [h2374, h2577, h2611, h2613, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2615 | h2615
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2616 | h2616
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2617 | h2617
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2618 | h2618
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2619 | h2619
                      · linarith only [h2611, h2619, h966, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h2619, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h2374, h2375, h2617, h2618, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2623 | h2623
                    · linarith only [h2374, h2577, h2617, h2623, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2625 | h2625
                      · linarith only [h2611, h2625, h966, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h2625, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h2374, h2577, h2615, h2616, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2629 | h2629
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2630 | h2630
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2631 | h2631
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2632 | h2632
                      · linarith only [h2611, h2632, h966, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h2632, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h2375, h2630, h2631, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2636 | h2636
                    · linarith only [h2374, h2577, h2630, h2636, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2638 | h2638
                      · linarith only [h2611, h2638, h966, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h2638, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h2374, h2629, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2642 | h2642
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2643 | h2643
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2644 | h2644
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2645 | h2645
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2646 | h2646
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2647 | h2647
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2648 | h2648
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2649 | h2649
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2650 | h2650
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2651 | h2651
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2652 | h2652
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2653 | h2653
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2654 | h2654
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2655 | h2655
                                · linarith only [h2374, h2642, h2647, h2655, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                · linarith only [h2374, h2642, h2646, h2647, h2653, h2655, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · linarith only [h2374, h2654, hc02, hlam, hphi, ht23, u3elo4]
                            · linarith only [h2374, h2642, h2646, h2653, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h2374, h2642, h2646, h2647, h2652, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h2374, h2642, h2645, h2646, h2647, h2651, hlam]
                      · linarith only [h2374, h2642, h2644, h2647, h2650, hlam]
                    · linarith only [h2374, h2643, h2647, h2649, hc12, hlam, hphi, ht23, u3elo1]
                  · linarith only [h2374, h2642, h2647, h2648, hlam]
                · linarith only [h0, h2647, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2666 | h2666
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2667 | h2667
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2668 | h2668
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2669 | h2669
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2670 | h2670
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2671 | h2671
                          · linarith only [h1840, h2646, h2669, h2671, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2673 | h2673
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2674 | h2674
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2675 | h2675
                                · linarith only [h2642, h2671, h2675, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2677 | h2677
                                  · linarith only [h1840, h2374, h2643, h2666, h2671, h2673, h2675, h2677, hc01, hlam, hphi, ht12, ht23, u3elo1]
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
                                      linarith only [h966, hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h1840, hlam, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2211, hlam, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2374, h2666, hc01, hlam, hphi, ht12, ht23, p2679_1, u3elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2374, hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h1840, h2374, h2666, hc01, hlam, hphi, ht12, ht23, p2679_1, u3elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2374, h2666, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2679_1, u3elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2374, h2666, hc01, hlam, hphi, ht12, ht23, p2679_1, u3elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2374, h2666, hc02, hlam, hphi, ht23, p2679_1, u3elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h1840, h2374, h2666, hc01, hlam, hphi, ht12, ht23, p2679_1, u3elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2211, h2374, h2666, hc01, hlam, hphi, ht12, ht23, p2679_1, u3elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h1840, h2671, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2642, hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2644, hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2646, hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2211, h2670, hc01, hlam, hphi, ht12, ht23, p2679_1, u3elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2643, hlam, p2679_1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2645, hlam, p2679_0]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [h2374, h2643, h2666, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2679_1, u3elo1]
                                    · have p2679_0 := h2679c.1
                                      have p2679_1 := h2679c.2.1
                                      have p2679_2 := h2679c.2.2.1
                                      have p2679_3 := h2679c.2.2.2
                                      linarith only [hlam, p2679_0]
                              · linarith only [h2374, h2674, hc02, hlam, hphi, ht23, u3elo4]
                            · linarith only [h2374, h2673, hc02, hlam, hphi, ht23, u3elo3]
                        · linarith only [h2645, h2670, hc13, hlam, hphi, u3elo0]
                      · linarith only [h2669, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h2374, h2643, h2668, hc12, hc23, hlam, hphi]
                  · linarith only [h2374, h2642, h2666, h2667, hlam]
                · linarith only [h0, h2666, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2374, h2643, h2645, hlam]
          · linarith only [h2374, h2642, h2644, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2714 | h2714
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2715 | h2715
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2716 | h2716
              · linarith only [h2642, h2643, h2716, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2718 | h2718
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2719 | h2719
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2720 | h2720
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2721 | h2721
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2722 | h2722
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2723 | h2723
                          · linarith only [h1840, h2716, h2721, h2723, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2725 | h2725
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2726 | h2726
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2727 | h2727
                                · linarith only [h2642, h2723, h2727, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2729 | h2729
                                  · linarith only [h1840, h2723, h2729, hc01, hlam, hphi, ht12, ht23, u3elo3]
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
                                      linarith only [h966, hlam, p2731_0]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h1840, hlam, p2731_1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2211, hlam, p2731_1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2643, h2720, h2722, hc01, hlam, hphi, ht12, ht23, p2731_1, u3elo1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [hlam, p2731_0]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2374, hlam, p2731_0]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2643, h2720, h2722, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2731_1, u3elo1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2643, hlam, p2731_0]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2374, h2718, hc01, hlam, hphi, ht12, ht23, p2731_1, u3elo1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2374, h2718, hc02, hlam, hphi, ht23, p2731_1, u3elo1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [hlam, p2731_0]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h1840, h2374, h2718, hc01, hlam, hphi, ht12, ht23, p2731_1, u3elo1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2211, h2374, h2718, hc01, hlam, hphi, ht12, ht23, p2731_1, u3elo1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h1840, h2723, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2731_1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2642, hlam, p2731_0]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2714, hlam, p2731_0]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [hlam, p2731_0]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2716, hlam, p2731_0]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2211, h2722, hc01, hlam, hphi, ht12, ht23, p2731_1, u3elo1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2642, h2643, h2720, h2722, h2725, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2731_1, u3elo1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h2715, hlam, p2731_0]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [h1840, h2643, h2720, h2722, hc01, hlam, hphi, ht12, ht23, p2731_1, u3elo1]
                                    · have p2731_0 := h2731c.1
                                      have p2731_1 := h2731c.2.1
                                      have p2731_2 := h2731c.2.2.1
                                      have p2731_3 := h2731c.2.2.2
                                      linarith only [hlam, p2731_0]
                              · linarith only [h2374, h2715, h2726, hlam]
                            · linarith only [h2374, h2725, hc02, hlam, hphi, ht23, u3elo3]
                        · linarith only [h2715, h2722, hc13, hlam, hphi, u3elo0]
                      · linarith only [h2721, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h2374, h2642, h2718, h2720, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h2374, h2642, h2718, h2719, hlam]
                · linarith only [h0, h2718, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2764 | h2764
              · linarith only [h2642, h2643, h2764, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2766 | h2766
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2767 | h2767
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2768 | h2768
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2769 | h2769
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2770 | h2770
                        · linarith only [h2715, h2770, hc03, hlam, hphi, u3elo1]
                        · linarith only [h2770, h966, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h2374, h2642, h2766, h2769, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h2374, h2642, h2766, h2768, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h2374, h2642, h2766, h2767, hlam]
                · linarith only [h0, h2766, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h2374, h2642, h2714, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2778 | h2778
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2779 | h2779
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2780 | h2780
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2781 | h2781
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2782 | h2782
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2783 | h2783
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2784 | h2784
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2785 | h2785
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2786 | h2786
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2787 | h2787
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2788 | h2788
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2789 | h2789
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2790 | h2790
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2791 | h2791
                                  · rcases h0bigk with h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h0, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h966, hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h1840, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2211, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2642, h2783, hc01, hc14, hlam, hphi, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2374, hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2642, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2211, h2642, h2783, hc01, hc14, hlam, hphi, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h966, hc01, hlam, hphi, ht12, ht23, p2792_1, u3elo1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2374, h2778, h2782, h2789, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2792_1, u3elo1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2374, h2642, h2778, h2782, h2789, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2792_1, u3elo1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2211, h2374, h2782, hc01, hlam, hphi, ht12, ht23, p2792_1, u3elo1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2374, h2779, h2782, hc01, hlam, hphi, ht12, ht23, p2792_1, u3elo1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2778, h2789, hc35, hlam, hphi, ht0b, ht5b, p2792_1, u0elo3]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2779, hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2211, h2374, h2779, h2782, hc01, hlam, hphi, ht12, ht23, p2792_1, u3elo1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2374, h2778, h2782, hc01, hlam, hphi, ht12, ht23, p2792_1, u3elo1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2778, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2780, hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2781, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [hlam, p2792_0]
                                  · linarith only [h2642, h2778, h2783, h2785, h2790, h2791, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h2374, h2642, h2779, h2781, h2782, h2790, hc02, hlam, hphi, ht23, u3elo1]
                              · linarith only [h2374, h2778, h2789, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                            · linarith only [h2374, h2778, h2788, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h1840, h2779, h2781, h2787, h966, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h2786, h966, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h2374, h2779, h2782, h2785, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2642, h2778, h2784, hc12, hc24, hlam, hphi]
                  · linarith only [h2374, h2782, h2783, hc02, hc24, hlam, hphi]
                · linarith only [h0, h2782, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h2642, h2778, h2781, hlam]
            · linarith only [h2374, h2778, h2780, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2830 | h2830
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2831 | h2831
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2832 | h2832
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2833 | h2833
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2834 | h2834
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2835 | h2835
                      · linarith only [h2374, h2779, h2835, hc02, hlam, hphi, ht23, u3elo1]
                      · linarith only [h2835, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h2374, h2778, h2832, h2834, hlam]
                  · linarith only [h2211, h2374, h2778, h2832, h2833, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2832, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h2642, h2778, h2831, hlam]
            · linarith only [h2374, h2778, h2830, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2843 | h2843
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2844 | h2844
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2845 | h2845
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2846 | h2846
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2847 | h2847
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2848 | h2848
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2849 | h2849
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2850 | h2850
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2851 | h2851
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2852 | h2852
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2853 | h2853
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2854 | h2854
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2855 | h2855
                                  · rcases h0bigk with h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [hlam, p2856_0]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h0, hlam, p2856_1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h966, hlam, p2856_0]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h1840, hlam, p2856_1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h2211, hlam, p2856_1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h2778, h2848, hc01, hc15, hlam, hphi, p2856_1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [hlam, p2856_0]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h2374, hlam, p2856_0]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h2642, hlam, p2856_1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h2778, hlam, p2856_0]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, p2856_1, u3elo0]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h2374, h2846, hc02, hlam, hphi, ht23, p2856_1, u3elo1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [hlam, p2856_0]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h2374, h2843, h2846, h2855, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2856_1, u3elo1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h0, h2374, h2778, h2846, hc01, hlam, hphi, ht12, ht23, p2856_1, u3elo1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h1840, h2849, hc01, hlam, hphi, ht12, ht23, p2856_1, u3elo1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h0, h2642, h2847, h2849, hc01, hlam, hphi, ht12, ht23, p2856_1, u3elo1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h2843, hlam, p2856_0]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [hlam, p2856_0]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h0, h2642, h2778, h2847, h2849, hc01, hlam, hphi, ht12, ht23, p2856_1, u3elo1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h2374, h2844, h2846, hc01, hlam, hphi, ht12, ht23, p2856_1, u3elo1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h0, h2374, h2844, h2846, hc01, hlam, hphi, ht12, ht23, p2856_1, u3elo1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h2844, hlam, p2856_0]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [h2845, hlam, p2856_1]
                                    · have p2856_0 := h2856c.1
                                      have p2856_1 := h2856c.2.1
                                      have p2856_2 := h2856c.2.2.1
                                      have p2856_3 := h2856c.2.2.2
                                      linarith only [hlam, p2856_0]
                                  · rcases h0bigk with h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [hlam, p2882_0]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h0, hlam, p2882_1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h966, hlam, p2882_0]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h1840, hlam, p2882_1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2211, hlam, p2882_1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2374, h2846, hc01, hlam, hphi, ht12, ht23, p2882_1, u3elo1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [hlam, p2882_0]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2374, hlam, p2882_0]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2642, hlam, p2882_1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2778, hlam, p2882_0]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2374, h2846, hc01, hlam, hphi, ht12, ht23, p2882_1, u3elo1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2374, h2846, hc02, hlam, hphi, ht23, p2882_1, u3elo1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [hlam, p2882_0]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2374, h2845, h2846, h2855, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2882_1, u3elo1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2211, h2374, h2846, hc01, hlam, hphi, ht12, ht23, p2882_1, u3elo1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h1840, h2849, hc01, hlam, hphi, ht12, ht23, p2882_1, u3elo1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h0, h2642, h2847, h2849, hc01, hlam, hphi, ht12, ht23, p2882_1, u3elo1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2843, hlam, p2882_0]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [hlam, p2882_0]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h0, h2642, h2778, h2847, h2849, hc01, hlam, hphi, ht12, ht23, p2882_1, u3elo1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2211, h2849, h2851, hc01, hlam, hphi, ht12, ht23, p2882_1, u3elo1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h0, h2778, h2848, h2849, h2851, hc01, hlam, hphi, ht12, ht23, p2882_1, u3elo1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2844, hlam, p2882_0]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [h2845, hlam, p2882_1]
                                    · have p2882_0 := h2882c.1
                                      have p2882_1 := h2882c.2.1
                                      have p2882_2 := h2882c.2.2.1
                                      have p2882_3 := h2882c.2.2.2
                                      linarith only [hlam, p2882_0]
                                · linarith only [h2642, h2845, h2854, hlam]
                              · linarith only [h0, h2374, h2853, hc01, hlam, hphi, ht12, ht23, u3elo4]
                            · linarith only [h0, h2374, h2852, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · linarith only [h1840, h2843, h2845, h2851, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h2374, h2844, h2846, h2850, hlam]
                      · linarith only [h2374, h2843, h2846, h2849, hlam]
                    · linarith only [h0, h2374, h2846, h2848, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2374, h2846, h2847, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2846, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2917 | h2917
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2918 | h2918
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2919 | h2919
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2920 | h2920
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2921 | h2921
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2922 | h2922
                          · linarith only [h0, h2642, h2845, h2920, h2922, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2924 | h2924
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2925 | h2925
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2926 | h2926
                                · linarith only [h1840, h2922, h2926, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2928 | h2928
                                  · linarith only [h0, h2642, h2918, h2922, h2928, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                  · rcases h0bigk with h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [hlam, p2930_0]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h0, hlam, p2930_1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h966, hlam, p2930_0]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h1840, hlam, p2930_1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h2211, hlam, p2930_1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h2642, h2918, h2921, h2922, hc01, hc13, hlam, hphi, p2930_1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [hlam, p2930_0]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h2374, hlam, p2930_0]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h2642, hlam, p2930_1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h2778, hlam, p2930_0]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, p2930_1, u3elo0]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h2374, h2917, hc02, hlam, hphi, ht23, p2930_1, u3elo1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [hlam, p2930_0]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h0, h2374, h2642, h2917, hc01, hlam, hphi, ht12, ht23, p2930_1, u3elo1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h0, h2374, h2642, h2845, h2917, hc01, hlam, hphi, ht12, ht23, p2930_1, u3elo1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h1840, h2921, h2922, hc01, hlam, hphi, ht12, ht23, p2930_1, u3elo1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h0, h2642, h2918, h2921, h2922, hc01, hlam, hphi, ht12, ht23, p2930_1, u3elo1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h2843, hlam, p2930_0]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [hlam, p2930_0]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h2845, hlam, p2930_0]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h2211, h2921, hc01, hlam, hphi, ht12, ht23, p2930_1, u3elo1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h0, h2211, h2921, hc01, hlam, hphi, ht12, ht23, p2930_1, u3elo1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h2844, hlam, p2930_0]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [h1840, h2374, h2844, h2917, hc01, hlam, hphi, ht12, ht23, p2930_1, u3elo1]
                                    · have p2930_0 := h2930c.1
                                      have p2930_1 := h2930c.2.1
                                      have p2930_2 := h2930c.2.2.1
                                      have p2930_3 := h2930c.2.2.2
                                      linarith only [hlam, p2930_0]
                              · linarith only [h2374, h2844, h2925, hlam]
                            · linarith only [h0, h2374, h2924, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h2844, h2921, hc13, hlam, hphi, u3elo0]
                      · linarith only [h2374, h2843, h2917, h2920, hlam]
                    · linarith only [h0, h2374, h2917, h2919, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2374, h2917, h2918, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2917, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2963 | h2963
              · linarith only [h2843, h2844, h2963, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2965 | h2965
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2966 | h2966
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2967 | h2967
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2968 | h2968
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2969 | h2969
                        · linarith only [h2844, h2969, hc03, hlam, hphi, u3elo1]
                        · linarith only [h2969, h966, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h2374, h2843, h2965, h2968, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h2374, h2965, h2967, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2374, h2965, h2966, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2965, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2976 | h2976
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2977 | h2977
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2978 | h2978
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2979 | h2979
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2980 | h2980
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2981 | h2981
                      · linarith only [h2843, h2976, h2981, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h2981, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h2374, h2978, h2980, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2374, h2978, h2979, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2978, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h2843, h2976, h2977, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2988 | h2988
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2989 | h2989
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2990 | h2990
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2991 | h2991
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2992 | h2992
                      · linarith only [h0, h2374, h2843, h2992, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h2992, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h2374, h2989, h2991, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2374, h2989, h2990, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2989, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2998 | h2998
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2999 | h2999
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3000 | h3000
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3001 | h3001
                      · linarith only [h0, h2374, h2843, h3001, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h3001, h966, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h2374, h2998, h3000, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2374, h2998, h2999, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h2998, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 6014000 in
set_option maxHeartbeats 6014000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h966 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1840 | h1840
  · exact r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h966 h1840
  · exact r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h966 h1840

set_option maxHeartbeats 6014000 in
set_option maxHeartbeats 6014000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h966 | h966
  · exact r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x1_x0 m hb0 hb2 hb3 hb5 h0 h966
  · exact r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x1_x1 m hb0 hb2 hb3 hb5 h0 h966

set_option maxHeartbeats 6014000 in
set_option maxHeartbeats 6014000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
