import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h2250 | h2250
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2251 | h2251
    · linarith only [h0, h2251, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2253 | h2253
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2254 | h2254
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2255 | h2255
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2256 | h2256
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2257 | h2257
              · linarith only [h0, h2249, h2257, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2259 | h2259
                · linarith only [h2256, h2257, h2259, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2261 | h2261
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2262 | h2262
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2263 | h2263
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2264 | h2264
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2265 | h2265
                          · linarith only [h2249, h2251, h2257, h2263, h2265, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2267 | h2267
                            · linarith only [h2249, h2251, h2259, h2264, h2267, hlam]
                            · linarith only [h2249, h2251, h2264, h2267, hc34, hc45, hlam, hphi]
                        · linarith only [h2256, h2257, h2261, h2264, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h2255, h2263, hlam]
                    · linarith only [h0, h2254, h2262, hlam]
                  · linarith only [h0, h2255, h2261, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2274 | h2274
              · linarith only [h2250, h2251, h2256, h2274, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2276 | h2276
                · linarith only [h2250, h2251, h2276, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2278 | h2278
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2279 | h2279
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2280 | h2280
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2281 | h2281
                        · linarith only [h2249, h2251, h2256, h2280, h2281, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2283 | h2283
                          · linarith only [h2249, h2251, h2274, h2283, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2285 | h2285
                            · linarith only [h2250, h2251, h2276, h2285, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2287 | h2287
                              · linarith only [h2253, h2256, h2287, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2289 | h2289
                                · linarith only [h0, h2253, h2289, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2291 | h2291
                                  · linarith only [h2251, h2254, h2285, h2291, hc02, hlam, hphi, ht0b, ht5b, u5ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2293 | h2293
                                    · linarith only [h2250, h2251, h2278, h2281, h2285, h2293, hc23, hc34, hlam, hphi]
                                    · rcases h0bigk with h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [hlam, p2295_0]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h0, hlam, p2295_1]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2249, h2251, h2278, h2283, hc23, hc35, hlam, hphi, p2295_1]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2250, h2251, h2278, h2281, h2283, hc23, hc35, hlam, hphi, p2295_1]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2251, hlam, p2295_1]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        rcases p2295_3 (m.d 0 1) (by simp) with h2301 | h2301
                                        · linarith only [h0, h2301, hlam]
                                        · rcases p2295_3 (m.d 0 2) (by simp) with h2303 | h2303
                                          · rcases p2295_3 (m.d 0 3) (by simp) with h2304 | h2304
                                            · linarith only [h2253, h2304, hlam]
                                            · rcases p2295_3 (m.d 0 4) (by simp) with h2306 | h2306
                                              · linarith only [h2254, h2306, hlam]
                                              · rcases p2295_3 (m.d 0 5) (by simp) with h2308 | h2308
                                                · linarith only [h2255, h2308, hlam]
                                                · linarith only [h2251, h2308, hlam]
                                          · linarith only [h0, h2303, hlam]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [hlam, p2295_0]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        rcases p2295_3 (m.d 0 1) (by simp) with h2313 | h2313
                                        · linarith only [h0, h2313, hlam]
                                        · linarith only [h2249, h2313, hlam]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        rcases p2295_3 (m.d 0 1) (by simp) with h2316 | h2316
                                        · linarith only [h0, h2316, hlam]
                                        · linarith only [h2250, h2316, hlam]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h0, h2255, hc12, hlam, hphi, ht01, ht0b, ht5b, p2295_1, u5ehi2]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2249, hlam, p2295_1]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2253, hlam, p2295_1]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [hlam, p2295_0]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2256, hlam, p2295_1]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2274, hlam, p2295_1]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2250, hlam, p2295_0]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2254, hlam, p2295_0]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2250, h2251, h2283, hc03, hc35, hlam, hphi, p2295_1]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [hlam, p2295_0]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2276, hlam, p2295_0]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2249, h2251, h2278, h2283, hc23, hc35, hlam, hphi, p2295_1]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [h2255, hlam, p2295_1]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        rcases p2295_3 (m.d 0 1) (by simp) with h2332 | h2332
                                        · linarith only [h2251, h2332, hlam]
                                        · linarith only [h2249, h2332, hlam]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        rcases p2295_3 (m.d 0 1) (by simp) with h2335 | h2335
                                        · linarith only [h2251, h2335, hlam]
                                        · linarith only [h2250, h2335, hlam]
                                      · have p2295_0 := h2295c.1
                                        have p2295_1 := h2295c.2.1
                                        have p2295_2 := h2295c.2.2.1
                                        have p2295_3 := h2295c.2.2.2
                                        linarith only [hlam, p2295_0]
                      · linarith only [h0, h2255, h2280, hlam]
                    · linarith only [h0, h2255, h2279, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h0, h2255, h2278, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2342 | h2342
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2343 | h2343
              · linarith only [h0, h2249, h2343, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2345 | h2345
                · linarith only [h0, h2250, h2255, h2345, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2347 | h2347
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2348 | h2348
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2349 | h2349
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2350 | h2350
                        · linarith only [h0, h2249, h2255, h2349, h2350, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h2249, h2255, h2342, h2349, h2350, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2353 | h2353
                        · linarith only [h0, h2249, h2349, h2353, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h2249, h2342, h2347, h2349, h2353, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h2250, h2254, h2348, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h2249, h2253, h2342, h2347, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2358 | h2358
              · linarith only [h2342, h2358, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2360 | h2360
                · linarith only [h0, h2250, h2255, h2360, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2362 | h2362
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2363 | h2363
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2364 | h2364
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2365 | h2365
                        · linarith only [h0, h2249, h2255, h2364, h2365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2367 | h2367
                          · linarith only [h0, h2250, h2255, h2358, h2364, h2365, h2367, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2369 | h2369
                            · linarith only [h0, h2250, h2255, h2360, h2364, h2369, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2371 | h2371
                              · linarith only [h2249, h2342, h2362, h2371, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2373 | h2373
                                · linarith only [h0, h2249, h2255, h2342, h2362, h2364, h2367, h2373, hc01, hc34, hlam, hphi, ht12, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2375 | h2375
                                  · linarith only [h2254, h2255, h2364, h2369, h2375, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2377 | h2377
                                    · linarith only [h0, h2250, h2255, h2362, h2364, h2365, h2369, h2377, hc23, hc34, hlam, hphi]
                                    · rcases h0bigk with h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c | h2379c
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [hlam, p2379_0]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h0, hlam, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h0, h2249, h2255, h2362, h2364, h2367, hc23, hc35, hlam, hphi, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h0, h2249, h2255, h2342, h2362, h2364, h2367, h2377, hc23, hc45, hlam, hphi, ht34, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2251, hlam, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2255, h2364, h2367, h2377, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [hlam, p2379_0]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2249, h2255, h2362, h2364, h2367, h2377, hc23, hc45, hlam, hphi, ht34, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2249, h2255, h2342, h2362, h2364, h2367, h2377, hc23, hc45, hlam, hphi, ht34, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2255, hlam, p2379_0]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2249, hlam, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2253, hlam, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [hlam, p2379_0]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2342, hlam, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2358, hlam, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2250, hlam, p2379_0]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2254, hlam, p2379_0]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h0, h2249, h2250, h2255, h2362, h2364, h2367, h2377, hc23, hc45, hlam, hphi, ht34, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [hlam, p2379_0]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2360, hlam, p2379_0]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h2249, h2251, h2362, h2367, h2377, hc23, hc45, hlam, hphi, ht34, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [h0, h2249, h2255, h2362, h2364, h2367, h2377, hc23, hc45, hlam, hphi, ht34, p2379_1]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        rcases p2379_3 (m.d 0 1) (by simp) with h2402 | h2402
                                        · linarith only [h2251, h2402, hlam]
                                        · linarith only [h2249, h2402, hlam]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        rcases p2379_3 (m.d 0 1) (by simp) with h2405 | h2405
                                        · linarith only [h2251, h2405, hlam]
                                        · linarith only [h2250, h2405, hlam]
                                      · have p2379_0 := h2379c.1
                                        have p2379_1 := h2379c.2.1
                                        have p2379_2 := h2379c.2.2.1
                                        have p2379_3 := h2379c.2.2.2
                                        linarith only [hlam, p2379_0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2409 | h2409
                        · linarith only [h0, h2249, h2364, h2409, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2411 | h2411
                          · linarith only [h0, h2250, h2364, h2409, h2411, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2413 | h2413
                            · linarith only [h0, h2250, h2364, h2413, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2415 | h2415
                              · linarith only [h0, h2253, h2342, h2364, h2415, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2417 | h2417
                                · linarith only [h2250, h2362, h2409, h2411, h2417, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                                · linarith only [h0, h2250, h2362, h2364, h2409, h2417, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h2249, h2254, h2362, h2363, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h2253, h2362, hlam]
        · linarith only [h0, h2250, h2254, hlam]
      · linarith only [h0, h2249, h2253, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2424 | h2424
    · linarith only [h0, h2424, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2426 | h2426
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2427 | h2427
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2428 | h2428
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2429 | h2429
            · linarith only [h2249, h2250, h2429, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2431 | h2431
              · linarith only [h2429, h2431, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2433 | h2433
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2434 | h2434
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2435 | h2435
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2436 | h2436
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2437 | h2437
                        · linarith only [h2249, h2250, h2429, h2435, h2437, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2439 | h2439
                          · linarith only [h2249, h2250, h2431, h2437, h2439, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2441 | h2441
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2442 | h2442
                              · linarith only [h2250, h2433, h2437, h2442, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2444 | h2444
                                · linarith only [h2249, h2424, h2434, h2439, h2444, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2446 | h2446
                                  · linarith only [h2427, h2446, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2448 | h2448
                                    · rcases h0bigk with h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [hlam, p2449_0]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h0, hlam, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2424, h2437, h2441, hc03, hc34, hlam, hphi, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2250, hlam, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2424, hlam, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        rcases p2449_3 (m.d 0 1) (by simp) with h2455 | h2455
                                        · linarith only [h0, h2455, hlam]
                                        · rcases p2449_3 (m.d 0 2) (by simp) with h2457 | h2457
                                          · rcases p2449_3 (m.d 0 3) (by simp) with h2458 | h2458
                                            · linarith only [h2426, h2458, hlam]
                                            · rcases p2449_3 (m.d 0 4) (by simp) with h2460 | h2460
                                              · linarith only [h2427, h2460, hlam]
                                              · linarith only [h2250, h2460, hlam]
                                          · linarith only [h0, h2457, hlam]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [hlam, p2449_0]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        rcases p2449_3 (m.d 0 1) (by simp) with h2465 | h2465
                                        · linarith only [h0, h2465, hlam]
                                        · linarith only [h2249, h2465, hlam]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h0, h2433, h2446, hc12, hlam, hphi, ht01, ht0b, ht5b, p2449_1, u5ehi2]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h0, h2433, h2446, hc12, hlam, hphi, ht01, ht0b, ht5b, p2449_1, u5ehi2]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2249, hlam, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2426, hlam, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [hlam, p2449_0]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2429, hlam, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2431, hlam, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2249, h2250, h2434, h2437, hc23, hc34, hlam, hphi, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2427, hlam, p2449_0]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        rcases p2449_3 (m.d 0 1) (by simp) with h2477 | h2477
                                        · linarith only [h2250, h2477, hlam]
                                        · linarith only [h2249, h2477, hlam]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [hlam, p2449_0]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2250, h2433, h2437, h2446, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2449_1, u5ehi2]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2249, h2424, h2434, h2437, h2441, hc23, hc34, hlam, hphi, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2428, hlam, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        rcases p2449_3 (m.d 0 1) (by simp) with h2484 | h2484
                                        · linarith only [h2424, h2484, hlam]
                                        · linarith only [h2249, h2484, hlam]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [h2433, hlam, p2449_1]
                                      · have p2449_0 := h2449c.1
                                        have p2449_1 := h2449c.2.1
                                        have p2449_2 := h2449c.2.2.1
                                        have p2449_3 := h2449c.2.2.2
                                        linarith only [hlam, p2449_0]
                                    · linarith only [h2249, h2250, h2434, h2437, h2448, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h2250, h2433, h2441, hlam]
                      · linarith only [h0, h2427, h2433, h2436, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h2427, h2433, h2435, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h2427, h2433, h2434, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2494 | h2494
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2495 | h2495
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2496 | h2496
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2497 | h2497
                        · linarith only [h2249, h2250, h2433, h2497, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2499 | h2499
                          · linarith only [h2249, h2250, h2433, h2499, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2501 | h2501
                            · linarith only [h2249, h2250, h2433, h2494, h2497, h2501, hc23, hc34, hlam, hphi]
                            · linarith only [h2249, h2250, h2494, h2501, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h2428, h2496, hlam]
                    · linarith only [h0, h2427, h2495, hlam]
                  · linarith only [h0, h2428, h2494, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2507 | h2507
            · linarith only [h2249, h2250, h2507, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2509 | h2509
              · linarith only [h0, h2249, h2509, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2511 | h2511
                · linarith only [h2427, h2428, h2511, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2513 | h2513
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2514 | h2514
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2515 | h2515
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2516 | h2516
                        · linarith only [h2249, h2250, h2427, h2428, h2507, h2515, h2516, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2518 | h2518
                          · linarith only [h2249, h2250, h2427, h2428, h2509, h2515, h2518, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2520 | h2520
                            · linarith only [h2249, h2250, h2511, h2516, h2520, hc13, hc34, hlam, hphi]
                            · linarith only [h2249, h2250, h2513, h2520, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2523 | h2523
                        · linarith only [h0, h2249, h2515, h2523, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2525 | h2525
                          · linarith only [h2249, h2250, h2514, h2515, h2525, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2527 | h2527
                            · linarith only [h2514, h2515, h2527, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h2249, h2250, h2513, h2527, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h2249, h2427, h2514, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h2426, h2513, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2532 | h2532
          · linarith only [h2427, h2532, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2534 | h2534
            · linarith only [h0, h2249, h2427, h2534, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2536 | h2536
              · linarith only [h0, h2249, h2427, h2536, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2538 | h2538
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2539 | h2539
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2540 | h2540
                    · linarith only [h2427, h2538, h2540, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2542 | h2542
                      · linarith only [h2532, h2540, h2542, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2544 | h2544
                        · linarith only [h2534, h2538, h2544, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2546 | h2546
                          · linarith only [h0, h2249, h2250, h2536, h2538, h2540, h2544, h2546, hc03, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2548 | h2548
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2549 | h2549
                              · linarith only [h2249, h2250, h2538, h2539, h2544, h2549, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h0, h2249, h2540, h2549, hc13, hc34, hlam, hphi]
                            · linarith only [h2250, h2538, h2548, hlam]
                  · linarith only [h0, h2249, h2426, h2539, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2554 | h2554
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2555 | h2555
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2556 | h2556
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2557 | h2557
                        · linarith only [h0, h2249, h2427, h2555, h2557, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2559 | h2559
                          · linarith only [h0, h2249, h2427, h2555, h2559, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2561 | h2561
                            · linarith only [h2249, h2250, h2538, h2557, h2561, hc13, hc34, hlam, hphi]
                            · linarith only [h2249, h2250, h2554, h2561, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h2427, h2555, h2556, hc02, hc25, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2565 | h2565
                      · linarith only [h2555, h2565, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2567 | h2567
                        · linarith only [h0, h2249, h2555, h2567, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2569 | h2569
                          · linarith only [h0, h2249, h2555, h2569, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2571 | h2571
                            · linarith only [h2249, h2250, h2538, h2554, h2567, h2571, hc23, hc34, hlam, hphi]
                            · linarith only [h2249, h2250, h2554, h2571, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2249, h2426, h2427, h2554, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h2249, h2426, hlam]

set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h2577 | h2577
  · linarith only [h2249, h2577, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2579 | h2579
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2580 | h2580
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2581 | h2581
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2582 | h2582
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2583 | h2583
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2584 | h2584
              · linarith only [h0, h2576, h2584, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2586 | h2586
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2587 | h2587
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2588 | h2588
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2589 | h2589
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2590 | h2590
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2591 | h2591
                          · linarith only [h2576, h2577, h2584, h2586, h2590, h2591, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2593 | h2593
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2594 | h2594
                              · linarith only [h2579, h2594, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2596 | h2596
                                · linarith only [h2576, h2577, h2587, h2591, h2596, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2598 | h2598
                                  · linarith only [h2577, h2583, h2591, h2593, h2594, h2598, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                  · rcases h0bigk with h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c | h2600c
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [hlam, p2600_0]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h0, hlam, p2600_1]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2249, hlam, p2600_0]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2576, h2577, h2587, h2591, h2593, hc34, hc45, hlam, hphi, p2600_1]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2577, hlam, p2600_1]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      rcases p2600_3 (m.d 0 1) (by simp) with h2606 | h2606
                                      · linarith only [h0, h2606, hlam]
                                      · rcases p2600_3 (m.d 0 2) (by simp) with h2608 | h2608
                                        · rcases p2600_3 (m.d 0 3) (by simp) with h2609 | h2609
                                          · linarith only [h2579, h2609, hlam]
                                          · linarith only [h2249, h2609, hlam]
                                        · linarith only [h0, h2608, hlam]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [hlam, p2600_0]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h0, h2583, h2594, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2600_1]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      rcases p2600_3 (m.d 0 1) (by simp) with h2615 | h2615
                                      · linarith only [h0, h2615, hlam]
                                      · linarith only [h2576, h2615, hlam]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h0, h2583, h2593, h2594, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2600_1]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      rcases p2600_3 (m.d 0 1) (by simp) with h2619 | h2619
                                      · linarith only [h2249, h2619, hlam]
                                      · rcases p2600_3 (m.d 0 2) (by simp) with h2621 | h2621
                                        · rcases p2600_3 (m.d 0 3) (by simp) with h2622 | h2622
                                          · rcases p2600_3 (m.d 0 4) (by simp) with h2623 | h2623
                                            · linarith only [h2582, h2623, hlam]
                                            · rcases p2600_3 (m.d 0 5) (by simp) with h2625 | h2625
                                              · linarith only [h2583, h2625, hlam]
                                              · linarith only [h2577, h2625, hlam]
                                          · linarith only [h2249, h2622, hlam]
                                        · linarith only [h0, h2621, hlam]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2579, hlam, p2600_1]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [hlam, p2600_0]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      rcases p2600_3 (m.d 0 1) (by simp) with h2632 | h2632
                                      · linarith only [h2249, h2632, hlam]
                                      · linarith only [h2576, h2632, hlam]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2249, h2583, h2586, h2593, h2594, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2600_1]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2576, hlam, p2600_0]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2580, hlam, p2600_0]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2582, hlam, p2600_0]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [hlam, p2600_0]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2584, hlam, p2600_0]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2576, h2577, h2587, h2591, h2593, hc34, hc45, hlam, hphi, p2600_1]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2581, hlam, p2600_1]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [h2583, hlam, p2600_0]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      rcases p2600_3 (m.d 0 1) (by simp) with h2644 | h2644
                                      · linarith only [h2577, h2644, hlam]
                                      · linarith only [h2576, h2644, hlam]
                                    · have p2600_0 := h2600c.1
                                      have p2600_1 := h2600c.2.1
                                      have p2600_2 := h2600c.2.2.1
                                      have p2600_3 := h2600c.2.2.2
                                      linarith only [hlam, p2600_0]
                            · linarith only [h2576, h2577, h2589, h2591, h2593, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h2249, h2583, h2590, hlam]
                      · linarith only [h2249, h2583, h2589, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · linarith only [h0, h2579, h2583, h2588, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h2579, h2583, h2587, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h0, h2579, h2583, h2586, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2654 | h2654
              · linarith only [h0, h2576, h2654, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2656 | h2656
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2657 | h2657
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2658 | h2658
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2659 | h2659
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2660 | h2660
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2661 | h2661
                          · linarith only [h2249, h2576, h2583, h2654, h2656, h2660, h2661, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2663 | h2663
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2664 | h2664
                              · linarith only [h2579, h2583, h2664, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2666 | h2666
                                · linarith only [h2249, h2576, h2583, h2657, h2660, h2661, h2666, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2668 | h2668
                                  · linarith only [h2249, h2576, h2583, h2657, h2660, h2661, h2663, h2668, hlam]
                                  · rcases h0bigk with h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c | h2670c
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [hlam, p2670_0]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h0, hlam, p2670_1]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2249, hlam, p2670_0]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2249, h2583, h2656, h2660, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2670_1]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2577, hlam, p2670_1]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      rcases p2670_3 (m.d 0 1) (by simp) with h2676 | h2676
                                      · linarith only [h0, h2676, hlam]
                                      · rcases p2670_3 (m.d 0 2) (by simp) with h2678 | h2678
                                        · rcases p2670_3 (m.d 0 3) (by simp) with h2679 | h2679
                                          · linarith only [h2579, h2679, hlam]
                                          · linarith only [h2249, h2679, hlam]
                                        · linarith only [h0, h2678, hlam]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [hlam, p2670_0]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      rcases p2670_3 (m.d 0 1) (by simp) with h2684 | h2684
                                      · linarith only [h0, h2684, hlam]
                                      · rcases p2670_3 (m.d 0 2) (by simp) with h2686 | h2686
                                        · rcases p2670_3 (m.d 0 3) (by simp) with h2687 | h2687
                                          · linarith only [h2579, h2687, hlam]
                                          · rcases p2670_3 (m.d 0 4) (by simp) with h2689 | h2689
                                            · linarith only [h2580, h2689, hlam]
                                            · rcases p2670_3 (m.d 0 5) (by simp) with h2691 | h2691
                                              · linarith only [h2581, h2691, hlam]
                                              · linarith only [h2583, h2691, hlam]
                                        · linarith only [h2579, h2686, hlam]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      rcases p2670_3 (m.d 0 1) (by simp) with h2695 | h2695
                                      · linarith only [h0, h2695, hlam]
                                      · linarith only [h2576, h2695, hlam]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2581, hc02, hlam, hphi, ht0b, ht5b, p2670_1, u5ehi2]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2583, h2656, h2660, hc01, hc12, hlam, hphi, p2670_1]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2579, hlam, p2670_1]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [hlam, p2670_0]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2576, h2583, h2656, h2657, h2660, h2663, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2670_1]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2583, hlam, p2670_1]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2576, hlam, p2670_0]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2580, hlam, p2670_0]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2582, hlam, p2670_0]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [hlam, p2670_0]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2654, hlam, p2670_0]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2576, h2577, h2657, h2661, h2663, hc34, hc45, hlam, hphi, p2670_1]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2581, hlam, p2670_1]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [h2249, h2576, h2583, h2656, h2657, h2660, h2663, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2670_1]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      rcases p2670_3 (m.d 0 1) (by simp) with h2712 | h2712
                                      · linarith only [h2577, h2712, hlam]
                                      · linarith only [h2576, h2712, hlam]
                                    · have p2670_0 := h2670c.1
                                      have p2670_1 := h2670c.2.1
                                      have p2670_2 := h2670c.2.2.1
                                      have p2670_3 := h2670c.2.2.2
                                      linarith only [hlam, p2670_0]
                            · linarith only [h2582, h2583, h2656, h2660, h2663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2717 | h2717
                          · linarith only [h2249, h2576, h2660, h2717, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2719 | h2719
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2720 | h2720
                              · linarith only [h2249, h2576, h2657, h2660, h2719, h2720, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2722 | h2722
                                · linarith only [h2249, h2576, h2657, h2660, h2717, h2722, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2724 | h2724
                                  · linarith only [h2249, h2576, h2657, h2660, h2717, h2719, h2724, hlam]
                                  · linarith only [h2249, h2576, h2657, h2660, h2719, h2724, hc34, hc45, hlam, hphi]
                            · linarith only [h2249, h2582, h2660, h2719, hc23, hc35, hlam, hphi]
                      · linarith only [h2249, h2576, h2582, h2659, hlam]
                    · linarith only [h0, h2581, h2658, hlam]
                  · linarith only [h0, h2581, h2657, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h0, h2581, h2656, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · linarith only [h2249, h2576, h2582, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2733 | h2733
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2734 | h2734
            · linarith only [h2579, h2581, h2734, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2736 | h2736
              · linarith only [h2249, h2576, h2736, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2738 | h2738
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2739 | h2739
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2740 | h2740
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2741 | h2741
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2742 | h2742
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2743 | h2743
                          · linarith only [h2249, h2576, h2579, h2581, h2736, h2740, h2743, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2745 | h2745
                            · linarith only [h2579, h2581, h2740, h2745, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h2579, h2581, h2733, h2740, h2745, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2748 | h2748
                          · linarith only [h2249, h2576, h2579, h2581, h2740, h2748, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2750 | h2750
                            · linarith only [h2579, h2581, h2740, h2750, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h2579, h2581, h2733, h2740, h2750, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h2249, h2576, h2733, h2741, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2754 | h2754
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2755 | h2755
                        · linarith only [h2738, h2740, h2755, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2757 | h2757
                          · linarith only [h2249, h2576, h2738, h2740, h2757, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2759 | h2759
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2760 | h2760
                              · linarith only [h2249, h2579, h2755, h2760, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2762 | h2762
                                · linarith only [h2576, h2577, h2739, h2757, h2762, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                                · linarith only [h2249, h2576, h2738, h2739, h2740, h2759, h2762, hc34, hc45, hlam, hphi]
                            · linarith only [h2733, h2734, h2759, hc23, hc35, hlam, hphi]
                      · linarith only [h2249, h2733, h2734, h2754, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h2580, h2739, hlam]
                · linarith only [h0, h2579, h2738, hlam]
          · linarith only [h2249, h2576, h2733, hlam]
      · linarith only [h0, h2576, h2580, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2771 | h2771
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2772 | h2772
        · linarith only [h2579, h2772, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2774 | h2774
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2775 | h2775
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2776 | h2776
              · linarith only [h0, h2576, h2579, h2776, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2778 | h2778
                · linarith only [h2579, h2775, h2778, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2780 | h2780
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2781 | h2781
                    · linarith only [h0, h2576, h2772, h2778, h2780, h2781, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2783 | h2783
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2784 | h2784
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2785 | h2785
                          · linarith only [h2576, h2785, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2787 | h2787
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2788 | h2788
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2789 | h2789
                                · linarith only [h0, h2576, h2780, h2781, h2785, h2789, hlam]
                                · linarith only [h0, h2576, h2781, h2789, hc14, hc45, hlam, hphi]
                              · linarith only [h0, h2576, h2579, h2775, h2780, h2787, h2788, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h2249, h2775, h2778, h2787, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h2249, h2775, h2784, hlam]
                      · linarith only [h2249, h2775, h2783, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · linarith only [h0, h2576, h2771, h2780, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2797 | h2797
              · linarith only [h0, h2576, h2797, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2799 | h2799
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2800 | h2800
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2801 | h2801
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2802 | h2802
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2803 | h2803
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2804 | h2804
                          · linarith only [h0, h2576, h2579, h2775, h2797, h2799, h2803, h2804, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2806 | h2806
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2807 | h2807
                              · linarith only [h0, h2579, h2775, h2799, h2807, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h2576, h2579, h2800, h2803, h2806, h2807, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h2576, h2579, h2774, h2800, h2806, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2811 | h2811
                          · linarith only [h2576, h2811, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2813 | h2813
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2814 | h2814
                              · linarith only [h2799, h2803, h2814, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2816 | h2816
                                · linarith only [h0, h2576, h2579, h2799, h2800, h2803, h2811, h2816, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2818 | h2818
                                  · linarith only [h0, h2576, h2579, h2799, h2800, h2803, h2811, h2813, h2818, hlam]
                                  · linarith only [h0, h2576, h2579, h2799, h2803, h2818, hc14, hc45, hlam, hphi]
                            · linarith only [h0, h2576, h2579, h2774, h2800, h2813, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h2249, h2576, h2774, h2802, hlam]
                    · linarith only [h0, h2579, h2799, h2801, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2576, h2579, h2799, h2800, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2825 | h2825
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2826 | h2826
                    · linarith only [h2799, h2826, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2828 | h2828
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2829 | h2829
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2830 | h2830
                          · linarith only [h2576, h2830, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2832 | h2832
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2833 | h2833
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2834 | h2834
                                · linarith only [h0, h2576, h2579, h2775, h2799, h2825, h2826, h2829, h2830, h2834, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h2576, h2825, h2826, h2832, h2834, hc34, hc45, hlam, hphi]
                              · linarith only [h2799, h2829, h2833, hlam]
                            · linarith only [h0, h2576, h2579, h2775, h2799, h2825, h2829, h2832, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2839 | h2839
                          · linarith only [h0, h2576, h2799, h2829, h2839, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2841 | h2841
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2842 | h2842
                              · linarith only [h0, h2576, h2799, h2825, h2829, h2841, h2842, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h2576, h2799, h2825, h2841, h2842, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h2576, h2799, h2825, h2841, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h2576, h2774, h2799, h2825, h2828, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h2771, h2825, hlam]
          · linarith only [h2249, h2576, h2774, hlam]
      · linarith only [h0, h2576, h2771, hlam]

set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2850 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  linarith only [h0, h2850, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]

end R2N4
