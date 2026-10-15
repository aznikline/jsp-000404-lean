import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_44S1
import Jsp000404.R1LeavesN7_44S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1800 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h2296 | h2296
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2297 | h2297
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2298 | h2298
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2299 | h2299
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2300 | h2300
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2301 | h2301
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2302 | h2302
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2303 | h2303
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2304 | h2304
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2305 | h2305
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2306 | h2306
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2307 | h2307
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2308 | h2308
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2309 | h2309
                            · linarith only [h0, h2296, h2309, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h1800, h2296, h2303, h2304, h2309, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h1800, h2298, h2302, h2308, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1800, h2301, h2307, hlam]
                      · linarith only [h0, h2296, h2305, h2306, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h1800, h2304, h2305, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2296, h2298, h2304, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2317 | h2317
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2318 | h2318
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2319 | h2319
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2320 | h2320
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2321 | h2321
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2322 | h2322
                            · linarith only [h2296, h2303, h2322, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2324 | h2324
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2325 | h2325
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2326 | h2326
                                  · linarith only [h1800, h2296, h2303, h2317, h2318, h2326, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2328 | h2328
                                    · linarith only [h0, h2298, h2301, h2303, h2328, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                    · rcases h0bigk with h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c | h2330c
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [hlam, p2330_0]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h0, hlam, p2330_1]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h1800, hlam, p2330_0]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h1800, h2317, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2330_1, u2elo1]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h1800, h2317, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2330_1, u2elo1]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2330_1, u2elo1]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [hlam, p2330_0]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h0, h1800, hc01, hlam, hphi, ht12, p2330_1, u2elo1]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        rcases p2330_3 (m.d 0 1) (by simp) with h2339 | h2339
                                        · linarith only [h0, h2339, hlam]
                                        · linarith only [h2296, h2339, hlam]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        rcases p2330_3 (m.d 0 1) (by simp) with h2342 | h2342
                                        · linarith only [h0, h2342, hlam]
                                        · linarith only [h2297, h2342, hlam]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h2297, h2318, h2322, h2324, hc34, hlam, hphi, ht0b, ht45, ht5b, p2330_1, u0elo2]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h2298, hlam, p2330_1]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [hlam, p2330_0]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        rcases p2330_3 (m.d 0 1) (by simp) with h2348 | h2348
                                        · linarith only [h1800, h2348, hlam]
                                        · linarith only [h2296, h2348, hlam]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        rcases p2330_3 (m.d 0 1) (by simp) with h2351 | h2351
                                        · linarith only [h1800, h2351, hlam]
                                        · linarith only [h2297, h2351, hlam]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h2296, hlam, p2330_0]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h2299, hlam, p2330_0]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h2301, hlam, p2330_0]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [hlam, p2330_0]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h2303, hlam, p2330_0]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h2297, hlam, p2330_0]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h2300, hlam, p2330_1]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h2302, hlam, p2330_0]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [h0, h2296, h2297, h2318, h2324, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2330_1, u2elo1]
                                      · have p2330_0 := h2330c.1
                                        have p2330_1 := h2330c.2.1
                                        have p2330_2 := h2330c.2.2.1
                                        have p2330_3 := h2330c.2.2.2
                                        linarith only [hlam, p2330_0]
                                · linarith only [h1800, h2297, h2317, h2321, h2325, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · linarith only [h1800, h2296, h2317, h2320, h2324, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h1800, h2302, h2321, hlam]
                        · linarith only [h1800, h2301, h2320, hlam]
                      · linarith only [h1800, h2317, h2319, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1800, h2317, h2318, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2317, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1800, h2297, h2302, hlam]
            · linarith only [h1800, h2296, h2301, hlam]
          · linarith only [h0, h2297, h2300, hlam]
        · linarith only [h1800, h2296, h2298, h2299, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2375 | h2375
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2376 | h2376
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2377 | h2377
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2378 | h2378
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2379 | h2379
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2380 | h2380
                  · linarith only [h2298, h2380, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2296, h2379, h2380, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2383 | h2383
                  · linarith only [h0, h2296, h2298, h2383, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2296, h2383, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h0, h2297, h2298, h2378, hlam]
            · linarith only [h0, h2296, h2298, h2377, hlam]
          · linarith only [h0, h2297, h2376, hlam]
        · linarith only [h0, h2296, h2375, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2390 | h2390
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2391 | h2391
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2392 | h2392
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2393 | h2393
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2394 | h2394
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2395 | h2395
                · linarith only [h2296, h2297, h2395, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2397 | h2397
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2398 | h2398
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2399 | h2399
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2400 | h2400
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2401 | h2401
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2402 | h2402
                            · linarith only [h2296, h2395, h2402, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2404 | h2404
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2405 | h2405
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2406 | h2406
                                  · linarith only [h2296, h2297, h2398, h2402, h2406, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2408 | h2408
                                    · linarith only [h2296, h2297, h2398, h2402, h2404, h2408, hlam]
                                    · rcases h0bigk with h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c | h2410c
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
                                        linarith only [h1800, hlam, p2410_0]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h2297, h2397, h2401, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2410_1, u2elo1]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h2297, hlam, p2410_1]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2410_1, u2elo1]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [hlam, p2410_0]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h0, h1800, hc01, hlam, hphi, ht12, p2410_1, u2elo1]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        rcases p2410_3 (m.d 0 1) (by simp) with h2419 | h2419
                                        · linarith only [h0, h2419, hlam]
                                        · linarith only [h2296, h2419, hlam]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h0, h2296, h2297, h2398, h2404, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2410_1, u2elo1]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h2296, h2398, h2404, hc34, hlam, hphi, ht0b, ht45, ht5b, p2410_1, u0elo2]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h2390, hlam, p2410_1]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [hlam, p2410_0]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        rcases p2410_3 (m.d 0 1) (by simp) with h2426 | h2426
                                        · linarith only [h1800, h2426, hlam]
                                        · linarith only [h2296, h2426, hlam]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h1800, h2296, h2297, h2397, h2398, h2404, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2410_1, u2elo1]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h2296, hlam, p2410_0]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h2391, hlam, p2410_0]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h2393, hlam, p2410_0]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [hlam, p2410_0]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h2395, hlam, p2410_0]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h2296, h2398, h2404, hc34, hlam, hphi, ht0b, ht45, ht5b, p2410_1, u0elo4]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h2392, hlam, p2410_1]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [h2394, hlam, p2410_0]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        rcases p2410_3 (m.d 0 1) (by simp) with h2438 | h2438
                                        · linarith only [h2297, h2438, hlam]
                                        · linarith only [h2296, h2438, hlam]
                                      · have p2410_0 := h2410c.1
                                        have p2410_1 := h2410c.2.1
                                        have p2410_2 := h2410c.2.2.1
                                        have p2410_3 := h2410c.2.2.2
                                        linarith only [hlam, p2410_0]
                                · linarith only [h1800, h2394, h2397, h2404, h2405, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h2296, h2297, h2397, h2400, h2401, h2404, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h1800, h2394, h2401, hlam]
                        · linarith only [h1800, h2393, h2400, hlam]
                      · linarith only [h0, h2296, h2398, h2399, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h1800, h2296, h2397, h2398, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2296, h2397, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2449 | h2449
                · linarith only [h1800, h2296, h2394, h2449, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2451 | h2451
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2452 | h2452
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2453 | h2453
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2454 | h2454
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2455 | h2455
                          · linarith only [h1800, h2296, h2394, h2451, h2452, h2455, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2457 | h2457
                            · linarith only [h2296, h2449, h2457, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2459 | h2459
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2460 | h2460
                                · linarith only [h1800, h2390, h2455, h2460, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2462 | h2462
                                  · linarith only [h1800, h2296, h2452, h2455, h2457, h2462, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2464 | h2464
                                    · linarith only [h1800, h2296, h2452, h2455, h2457, h2459, h2464, hlam]
                                    · linarith only [h1800, h2296, h2452, h2455, h2459, h2464, hc34, hc45, hlam, hphi]
                              · linarith only [h1800, h2393, h2455, h2459, hc23, hc35, hlam, hphi]
                        · linarith only [h1800, h2296, h2393, h2454, hlam]
                      · linarith only [h0, h2392, h2453, hlam]
                    · linarith only [h0, h2452, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2296, h2451, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h1800, h2296, h2393, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2473 | h2473
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2474 | h2474
              · linarith only [h2390, h2392, h2474, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2476 | h2476
                · linarith only [h0, h2296, h2392, h2476, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2478 | h2478
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2479 | h2479
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2480 | h2480
                      · linarith only [h1800, h2296, h2390, h2392, h2479, h2480, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h2296, h2479, h2480, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h1800, h2296, h2478, h2479, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h2390, h2392, h2478, hc12, hlam, hphi, u2elo4]
            · linarith only [h1800, h2296, h2473, hlam]
        · linarith only [h0, h2296, h2391, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2487 | h2487
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2488 | h2488
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2489 | h2489
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2490 | h2490
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2491 | h2491
                · linarith only [h2296, h2297, h2491, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2493 | h2493
                  · linarith only [h2297, h2390, h2488, h2493, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2296, h2493, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h2390, h2488, h2490, hlam]
            · linarith only [h2296, h2297, h2390, h2488, h2489, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2498 | h2498
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2499 | h2499
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2500 | h2500
                · linarith only [h0, h2296, h2488, h2500, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2502 | h2502
                  · linarith only [h0, h2296, h2390, h2502, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2296, h2502, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2505 | h2505
                · linarith only [h1800, h2296, h2499, h2505, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2507 | h2507
                  · linarith only [h0, h2296, h2390, h2507, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2296, h2507, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h2296, h2390, h2498, hlam]
        · linarith only [h0, h2296, h2487, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2512 | h2512
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2513 | h2513
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2514 | h2514
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2515 | h2515
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2516 | h2516
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2517 | h2517
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2518 | h2518
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2519 | h2519
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2520 | h2520
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2521 | h2521
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2522 | h2522
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2523 | h2523
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2524 | h2524
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2525 | h2525
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2526 | h2526
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2527 | h2527
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2528 | h2528
                                    · linarith only [h2513, h2525, h2528, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h0, h2512, h2524, h2528, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · linarith only [h2296, h2512, h2519, h2522, h2524, h2527, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · linarith only [h2296, h2512, h2519, h2522, h2523, h2526, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2533 | h2533
                                · linarith only [h1800, h2516, h2519, h2525, h2533, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · linarith only [h2296, h2512, h2519, h2522, h2523, h2533, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h2296, h2518, h2524, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1800, h2517, h2523, hlam]
                        · linarith only [h1800, h2516, h2522, hlam]
                      · linarith only [h0, h2512, h2521, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                    · linarith only [h0, h2512, h2520, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h2512, h2519, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h2296, h2512, h2518, hlam]
              · linarith only [h1800, h2512, h2517, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2544 | h2544
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2545 | h2545
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2546 | h2546
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2547 | h2547
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2548 | h2548
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2549 | h2549
                        · linarith only [h1800, h2512, h2516, h2546, h2548, h2549, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2551 | h2551
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2552 | h2552
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2553 | h2553
                              · linarith only [h2513, h2549, h2553, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2555 | h2555
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2556 | h2556
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2557 | h2557
                                    · rcases h0bigk with h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [hlam, p2558_0]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h0, hlam, p2558_1]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h1800, hlam, p2558_0]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h2296, hlam, p2558_1]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h1800, h2549, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2558_1]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2558_1, u2elo1]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [hlam, p2558_0]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h0, h1800, h2512, h2548, h2555, h2557, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2558_1, u2elo1]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h0, h1800, h2512, h2516, h2548, h2555, h2557, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2558_1, u2elo1]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        rcases p2558_3 (m.d 0 1) (by simp) with h2568 | h2568
                                        · linarith only [h0, h2568, hlam]
                                        · linarith only [h2512, h2568, hlam]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h2512, h2548, h2555, h2557, hc45, hlam, hphi, ht0b, ht5b, p2558_1, u0elo2]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h2513, hlam, p2558_1]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [hlam, p2558_0]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h2516, hlam, p2558_1]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        rcases p2558_3 (m.d 0 1) (by simp) with h2575 | h2575
                                        · linarith only [h1800, h2575, hlam]
                                        · linarith only [h2512, h2575, hlam]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h2512, h2548, h2555, h2557, hc45, hlam, hphi, ht0b, ht5b, p2558_1, u0elo3]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h2514, hlam, p2558_0]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h0, h1800, h2512, h2514, h2548, h2555, h2557, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2558_1, u2elo1]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [hlam, p2558_0]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        rcases p2558_3 (m.d 0 1) (by simp) with h2582 | h2582
                                        · linarith only [h2296, h2582, hlam]
                                        · linarith only [h2512, h2582, hlam]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h2512, hlam, p2558_0]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h2515, hlam, p2558_1]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h2544, hlam, p2558_0]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [h2545, hlam, p2558_1]
                                      · have p2558_0 := h2558c.1
                                        have p2558_1 := h2558c.2.1
                                        have p2558_2 := h2558c.2.2.1
                                        have p2558_3 := h2558c.2.2.2
                                        linarith only [hlam, p2558_0]
                                    · linarith only [h1800, h2512, h2548, h2549, h2555, h2557, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                  · linarith only [h1800, h2512, h2549, h2552, h2556, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h1800, h2544, h2549, h2555, hc23, hc34, hlam, hphi]
                            · linarith only [h1800, h2514, h2545, h2549, h2552, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h1800, h2512, h2544, h2548, h2551, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h0, h2548, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h2512, h2547, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h2512, h2546, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h1800, h2512, h2516, h2545, hlam]
              · linarith only [h1800, h2512, h2544, hlam]
          · linarith only [h0, h2512, h2515, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2601 | h2601
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2602 | h2602
            · linarith only [h2513, h2514, h2602, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2604 | h2604
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2605 | h2605
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2606 | h2606
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2607 | h2607
                    · linarith only [h1800, h2513, h2514, h2607, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h2512, h2607, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h2512, h2606, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h1800, h2512, h2513, h2514, h2605, hlam]
              · linarith only [h1800, h2512, h2604, hlam]
          · linarith only [h1800, h2512, h2513, h2601, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2614 | h2614
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2615 | h2615
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2616 | h2616
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2617 | h2617
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2618 | h2618
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2619 | h2619
                  · linarith only [h2513, h2619, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2512, h2619, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h2296, h2512, h2618, hlam]
              · linarith only [h2296, h2512, h2513, h2614, h2617, hlam]
            · linarith only [h2513, h2614, h2616, hlam]
          · linarith only [h2296, h2512, h2614, h2615, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2626 | h2626
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2627 | h2627
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2628 | h2628
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2629 | h2629
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2630 | h2630
                  · linarith only [h0, h2512, h2513, h2630, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h2512, h2630, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h0, h2512, h2614, h2629, hlam]
              · linarith only [h1800, h2512, h2628, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2635 | h2635
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2636 | h2636
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2637 | h2637
                  · linarith only [h0, h2513, h2637, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2512, h2637, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h0, h2512, h2513, h2627, h2636, hlam]
              · linarith only [h0, h2512, h2513, h2635, hlam]
          · linarith only [h0, h2512, h2626, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2643 | h2643
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2644 | h2644
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2645 | h2645
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2646 | h2646
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2647 | h2647
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2648 | h2648
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2649 | h2649
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2650 | h2650
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2651 | h2651
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2652 | h2652
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2653 | h2653
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2654 | h2654
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2655 | h2655
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2656 | h2656
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2657 | h2657
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2658 | h2658
                                    · linarith only [h2643, h2655, h2658, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h0, h2643, h2655, h2657, h2658, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2661 | h2661
                                    · linarith only [h0, h2643, h2646, h2657, h2661, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                    · rcases h0bigk with h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [hlam, p2663_0]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h0, hlam, p2663_1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h1800, hlam, p2663_0]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h2296, hlam, p2663_1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h2512, hlam, p2663_1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2663_1, u2elo1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [hlam, p2663_0]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h0, h1800, hc01, hlam, hphi, ht12, p2663_1, u2elo1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h0, h2512, h2648, hc01, hlam, hphi, ht12, p2663_1, u2elo1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h0, h2512, hc01, hlam, hphi, ht12, p2663_1, u2elo1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h1800, h2649, hc01, hlam, hphi, ht12, p2663_1, u2elo1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h2643, hlam, p2663_1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [hlam, p2663_0]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h1800, h2512, h2648, h2649, hc01, hlam, hphi, ht12, p2663_1, u2elo1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h1800, h2512, h2649, hc01, hlam, hphi, ht12, p2663_1, u2elo1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h2296, h2649, h2652, hc01, hlam, hphi, ht12, p2663_1, u2elo1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h2644, hlam, p2663_0]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h2646, hlam, p2663_0]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [hlam, p2663_0]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h2296, h2512, h2649, h2652, hc01, hlam, hphi, ht12, p2663_1, u2elo1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h2512, h2649, h2652, h2654, hc01, hlam, hphi, ht12, p2663_1, u2elo1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h2645, hlam, p2663_1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h2647, hlam, p2663_0]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [h2648, hlam, p2663_1]
                                      · have p2663_0 := h2663c.1
                                        have p2663_1 := h2663c.2.1
                                        have p2663_2 := h2663c.2.2.1
                                        have p2663_3 := h2663c.2.2.2
                                        linarith only [hlam, p2663_0]
                                · linarith only [h1800, h2647, h2649, h2655, h2656, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2690 | h2690
                                · linarith only [h1800, h2646, h2649, h2655, h2690, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2692 | h2692
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2693 | h2693
                                    · rcases h0bigk with h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [hlam, p2694_0]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h0, hlam, p2694_1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h1800, hlam, p2694_0]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h2296, hlam, p2694_1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h2512, hlam, p2694_1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2694_1, u2elo1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [hlam, p2694_0]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h0, h2646, h2690, h2693, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2694_1, u2elo1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h0, h2296, hc01, hlam, hphi, ht12, p2694_1, u2elo1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h0, h2512, hc01, hlam, hphi, ht12, p2694_1, u2elo1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h1800, h2649, hc01, hlam, hphi, ht12, p2694_1, u2elo1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h2643, hlam, p2694_1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [hlam, p2694_0]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h1800, h2644, h2649, h2692, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2694_1, u2elo1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h1800, h2512, h2649, hc01, hlam, hphi, ht12, p2694_1, u2elo1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h2296, h2649, h2652, hc01, hlam, hphi, ht12, p2694_1, u2elo1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h2644, hlam, p2694_0]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h2646, hlam, p2694_0]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [hlam, p2694_0]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h2296, h2647, h2649, h2652, h2690, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2694_1, u2elo1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h2512, h2649, h2652, h2654, hc01, hlam, hphi, ht12, p2694_1, u2elo1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h2645, hlam, p2694_1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h2647, hlam, p2694_0]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [h2648, hlam, p2694_1]
                                      · have p2694_0 := h2694c.1
                                        have p2694_1 := h2694c.2.1
                                        have p2694_2 := h2694c.2.2.1
                                        have p2694_3 := h2694c.2.2.2
                                        linarith only [hlam, p2694_0]
                                    · linarith only [h0, h2644, h2692, h2693, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2721 | h2721
                                    · linarith only [h1800, h2646, h2649, h2655, h2692, h2721, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                    · linarith only [h2296, h2648, h2649, h2652, h2655, h2721, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h2296, h2648, h2654, hlam]
                          · linarith only [h1800, h2647, h2653, hlam]
                        · linarith only [h1800, h2646, h2652, hlam]
                      · linarith only [h0, h2651, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h2650, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2649, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2730 | h2730
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2731 | h2731
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2732 | h2732
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2733 | h2733
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2734 | h2734
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2735 | h2735
                            · linarith only [h2296, h2648, h2731, h2735, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2737 | h2737
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2738 | h2738
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2739 | h2739
                                  · linarith only [h2296, h2644, h2735, h2739, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2741 | h2741
                                    · linarith only [h2296, h2643, h2735, h2737, h2741, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                    · rcases h0bigk with h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c | h2743c
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [hlam, p2743_0]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h0, hlam, p2743_1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h1800, hlam, p2743_0]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h2296, hlam, p2743_1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h2512, hlam, p2743_1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2743_1, u2elo1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [hlam, p2743_0]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h0, h1800, hc01, hlam, hphi, ht12, p2743_1, u2elo1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h0, h2296, hc01, hlam, hphi, ht12, p2743_1, u2elo1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h0, h2296, h2648, hc01, hlam, hphi, ht12, p2743_1, u2elo1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h1800, h2730, hc01, hlam, hphi, ht12, p2743_1, u2elo1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h2643, hlam, p2743_1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [hlam, p2743_0]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h1800, h2296, h2730, hc01, hlam, hphi, ht12, p2743_1, u2elo1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h1800, h2296, h2648, h2730, hc01, hlam, hphi, ht12, p2743_1, u2elo1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h2296, h2735, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2743_1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h2644, hlam, p2743_0]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h2646, hlam, p2743_0]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [hlam, p2743_0]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h2648, hlam, p2743_0]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h2512, h2730, h2734, hc01, hlam, hphi, ht12, p2743_1, u2elo1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h2645, hlam, p2743_1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h2647, hlam, p2743_0]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [h2296, h2512, h2730, h2734, hc01, hlam, hphi, ht12, p2743_1, u2elo1]
                                      · have p2743_0 := h2743c.1
                                        have p2743_1 := h2743c.2.1
                                        have p2743_2 := h2743c.2.2.1
                                        have p2743_3 := h2743c.2.2.2
                                        linarith only [hlam, p2743_0]
                                · linarith only [h1800, h2647, h2730, h2737, h2738, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2770 | h2770
                                · linarith only [h1800, h2646, h2730, h2737, h2770, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2772 | h2772
                                  · linarith only [h2296, h2735, h2772, hc01, hlam, hphi, ht12, u2elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2774 | h2774
                                    · linarith only [h1800, h2296, h2646, h2730, h2735, h2774, hc01, hlam, hphi, ht12, u2elo1]
                                    · rcases h0bigk with h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [hlam, p2776_0]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h0, hlam, p2776_1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h1800, hlam, p2776_0]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h2296, hlam, p2776_1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h2512, hlam, p2776_1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2776_1, u2elo1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [hlam, p2776_0]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h0, h2647, h2737, h2774, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2776_1, u2elo1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h0, h2646, h2737, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2776_1, u2elo1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h0, h2512, hc01, hlam, hphi, ht12, p2776_1, u2elo1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h1800, h2730, hc01, hlam, hphi, ht12, p2776_1, u2elo1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h2643, hlam, p2776_1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [hlam, p2776_0]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h1800, h2646, h2730, h2737, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2776_1, u2elo1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h1800, h2512, h2730, hc01, hlam, hphi, ht12, p2776_1, u2elo1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h2296, h2735, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2776_1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h2644, hlam, p2776_0]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h2646, hlam, p2776_0]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [hlam, p2776_0]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h2648, hlam, p2776_0]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h2512, h2730, h2734, hc01, hlam, hphi, ht12, p2776_1, u2elo1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h2645, hlam, p2776_1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h2647, hlam, p2776_0]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [h2296, h2512, h2730, h2734, hc01, hlam, hphi, ht12, p2776_1, u2elo1]
                                      · have p2776_0 := h2776c.1
                                        have p2776_1 := h2776c.2.1
                                        have p2776_2 := h2776c.2.2.1
                                        have p2776_3 := h2776c.2.2.2
                                        linarith only [hlam, p2776_0]
                          · linarith only [h1800, h2647, h2734, hlam]
                        · linarith only [h1800, h2646, h2733, hlam]
                      · linarith only [h0, h2645, h2732, hlam]
                    · linarith only [h0, h2644, h2731, hlam]
                  · linarith only [h0, h2730, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2807 | h2807
                · linarith only [h2646, h2647, h2807, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2809 | h2809
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2810 | h2810
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2811 | h2811
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2812 | h2812
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2813 | h2813
                          · linarith only [h2646, h2647, h2809, h2813, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2815 | h2815
                            · linarith only [h2296, h2807, h2810, h2815, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2817 | h2817
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2818 | h2818
                                · linarith only [h1800, h2643, h2813, h2818, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2820 | h2820
                                  · linarith only [h2644, h2807, h2820, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2822 | h2822
                                    · linarith only [h2296, h2815, h2822, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · rcases h0bigk with h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c | h2824c
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [hlam, p2824_0]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h0, hlam, p2824_1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h1800, hlam, p2824_0]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h2296, hlam, p2824_1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h2512, hlam, p2824_1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2824_1, u2elo1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [hlam, p2824_0]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h0, h2643, h2817, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2824_1, u2elo1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h0, h2296, hc01, hlam, hphi, ht12, p2824_1, u2elo1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h0, h2643, h2647, h2817, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2824_1, u2elo1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h1800, h2813, hc01, hc35, hlam, hphi, ht12, ht23, p2824_1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h2643, hlam, p2824_1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [hlam, p2824_0]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h1800, h2296, h2813, h2822, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2824_1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h2647, hlam, p2824_1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h0, h2644, hc01, hlam, hphi, ht12, p2824_1, u2elo1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h2644, hlam, p2824_0]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h2646, hlam, p2824_0]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [hlam, p2824_0]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h2807, hlam, p2824_0]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h2512, h2811, hc01, hlam, hphi, ht12, p2824_1, u2elo1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h2645, hlam, p2824_1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h1800, h2512, h2811, hc01, hlam, hphi, ht12, p2824_1, u2elo1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [h2296, h2512, h2811, hc01, hlam, hphi, ht12, p2824_1, u2elo1]
                                      · have p2824_0 := h2824c.1
                                        have p2824_1 := h2824c.2.1
                                        have p2824_2 := h2824c.2.2.1
                                        have p2824_3 := h2824c.2.2.2
                                        linarith only [hlam, p2824_0]
                              · linarith only [h1800, h2646, h2813, h2817, hc23, hc35, hlam, hphi]
                        · linarith only [h0, h1800, h2644, h2646, h2812, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h2645, h2811, hlam]
                    · linarith only [h0, h2810, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2809, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2855 | h2855
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2856 | h2856
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2857 | h2857
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2858 | h2858
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2859 | h2859
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2860 | h2860
                        · linarith only [h2646, h2855, h2857, h2860, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2862 | h2862
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2863 | h2863
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2864 | h2864
                              · linarith only [h2643, h2646, h2864, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2866 | h2866
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2867 | h2867
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2868 | h2868
                                    · rcases h0bigk with h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c | h2869c
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [hlam, p2869_0]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h0, hlam, p2869_1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h1800, hlam, p2869_0]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h2296, hlam, p2869_1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h2512, hlam, p2869_1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, p2869_1, u2elo0]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [hlam, p2869_0]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h0, h2643, h2866, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2869_1, u2elo1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h0, h2296, hc01, hlam, hphi, ht12, p2869_1, u2elo1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h0, h2512, hc01, hlam, hphi, ht12, p2869_1, u2elo1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h1800, h2860, hc01, hc34, hlam, hphi, ht12, ht23, p2869_1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h2643, hlam, p2869_1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [hlam, p2869_0]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h2646, hlam, p2869_1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h1800, h2512, h2860, hc01, hc34, hlam, hphi, ht12, ht23, p2869_1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h0, h2644, hc01, hlam, hphi, ht12, p2869_1, u2elo1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h2644, hlam, p2869_0]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h0, h1800, h2644, hc01, hlam, hphi, ht12, p2869_1, u2elo1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [hlam, p2869_0]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h0, h2512, h2644, hc01, hlam, hphi, ht12, p2869_1, u2elo1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h0, h2645, hc01, hlam, hphi, ht12, p2869_1, u2elo1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h2645, hlam, p2869_1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h2855, hlam, p2869_0]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [h2856, hlam, p2869_1]
                                      · have p2869_0 := h2869c.1
                                        have p2869_1 := h2869c.2.1
                                        have p2869_2 := h2869c.2.2.1
                                        have p2869_3 := h2869c.2.2.2
                                        linarith only [hlam, p2869_0]
                                    · linarith only [h2646, h2856, h2868, hlam]
                                  · linarith only [h2296, h2856, h2858, h2864, h2866, h2867, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · linarith only [h1800, h2855, h2860, h2866, hc23, hc34, hlam, hphi]
                            · linarith only [h2296, h2856, h2863, hlam]
                          · linarith only [h1800, h2855, h2862, hlam]
                      · linarith only [h0, h2859, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h2858, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2857, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2646, h2855, h2856, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2904 | h2904
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2905 | h2905
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2906 | h2906
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2907 | h2907
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2908 | h2908
                        · linarith only [h1800, h2646, h2905, h2908, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2910 | h2910
                          · linarith only [h1800, h2855, h2906, h2908, h2910, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2912 | h2912
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2913 | h2913
                              · linarith only [h2643, h2908, h2913, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2915 | h2915
                                · linarith only [h1800, h2644, h2910, h2913, h2915, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2917 | h2917
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2918 | h2918
                                    · rcases h0bigk with h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c | h2919c
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [hlam, p2919_0]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h0, hlam, p2919_1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h1800, hlam, p2919_0]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h2296, hlam, p2919_1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h2512, hlam, p2919_1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2919_1, u2elo1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [hlam, p2919_0]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h0, h1800, hc01, hlam, hphi, ht12, p2919_1, u2elo1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h0, h2296, hc01, hlam, hphi, ht12, p2919_1, u2elo1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h0, h2512, hc01, hlam, hphi, ht12, p2919_1, u2elo1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h1800, h2910, h2918, hc01, hc34, hlam, hphi, ht12, ht23, p2919_1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h2643, hlam, p2919_1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [hlam, p2919_0]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h2646, hlam, p2919_1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h2855, hlam, p2919_1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h2296, h2906, hc01, hlam, hphi, ht12, p2919_1, u2elo1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h2644, hlam, p2919_0]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h1800, h2296, h2906, hc01, hlam, hphi, ht12, p2919_1, u2elo1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [hlam, p2919_0]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h1800, h2296, h2855, h2906, hc01, hlam, hphi, ht12, p2919_1, u2elo1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h2512, h2906, h2912, hc01, hlam, hphi, ht12, p2919_1, u2elo1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h2645, hlam, p2919_1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h1800, h2512, h2906, h2912, hc01, hlam, hphi, ht12, p2919_1, u2elo1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [h2904, hlam, p2919_1]
                                      · have p2919_0 := h2919c.1
                                        have p2919_1 := h2919c.2.1
                                        have p2919_2 := h2919c.2.2.1
                                        have p2919_3 := h2919c.2.2.2
                                        linarith only [hlam, p2919_0]
                                    · linarith only [h0, h2644, h2917, h2918, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2946 | h2946
                                    · rcases h0bigk with h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c | h2947c
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [hlam, p2947_0]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h0, hlam, p2947_1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h1800, hlam, p2947_0]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h2296, hlam, p2947_1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h2512, hlam, p2947_1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p2947_1, u2elo1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [hlam, p2947_0]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h0, h1800, hc01, hlam, hphi, ht12, p2947_1, u2elo1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h0, h2904, h2913, h2917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2947_1, u2elo1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h0, h2512, hc01, hlam, hphi, ht12, p2947_1, u2elo1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h1800, h2910, h2946, hc01, hc34, hlam, hphi, ht12, ht23, p2947_1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h2643, hlam, p2947_1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [hlam, p2947_0]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h2646, hlam, p2947_1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h2855, hlam, p2947_1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h2296, h2906, hc01, hlam, hphi, ht12, p2947_1, u2elo1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h2644, hlam, p2947_0]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h1800, h2296, h2906, hc01, hlam, hphi, ht12, p2947_1, u2elo1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [hlam, p2947_0]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h2296, h2512, h2906, hc01, hlam, hphi, ht12, p2947_1, u2elo1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h2512, h2906, h2912, hc01, hlam, hphi, ht12, p2947_1, u2elo1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h2645, hlam, p2947_1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h1800, h2512, h2906, h2912, hc01, hlam, hphi, ht12, p2947_1, u2elo1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [h2904, hlam, p2947_1]
                                      · have p2947_0 := h2947c.1
                                        have p2947_1 := h2947c.2.1
                                        have p2947_2 := h2947c.2.2.1
                                        have p2947_3 := h2947c.2.2.2
                                        linarith only [hlam, p2947_0]
                                    · linarith only [h1800, h2296, h2646, h2904, h2906, h2946, hc01, hlam, hphi, ht12, u2elo1]
                            · linarith only [h2296, h2904, h2912, hlam]
                      · linarith only [h0, h2907, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1800, h2905, h2906, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2905, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2978 | h2978
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2979 | h2979
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2980 | h2980
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2981 | h2981
                        · linarith only [h1800, h2646, h2978, h2981, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2983 | h2983
                          · linarith only [h1800, h2855, h2979, h2981, h2983, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2985 | h2985
                            · linarith only [h2296, h2904, h2979, h2985, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2987 | h2987
                              · linarith only [h1800, h2643, h2981, h2987, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2989 | h2989
                                · linarith only [h0, h1800, h2644, h2983, h2987, h2989, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2991 | h2991
                                  · linarith only [h0, h2644, h2985, h2991, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2993 | h2993
                                    · linarith only [h1800, h2981, h2985, h2993, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h1800, h2981, h2993, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h2645, h2980, hlam]
                    · linarith only [h0, h2979, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2643, h2646, h2978, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2999 | h2999
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3000 | h3000
              · linarith only [h2643, h2645, h3000, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3002 | h3002
                · linarith only [h2643, h2645, h2999, h3002, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3004 | h3004
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3005 | h3005
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3006 | h3006
                      · linarith only [h2645, h3006, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h3006, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1800, h2644, h3004, h3005, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h2643, h2645, h3004, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3011 | h3011
              · linarith only [h2644, h2645, h2999, h3011, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3013 | h3013
                · linarith only [h2644, h2645, h3013, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3015 | h3015
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3016 | h3016
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3017 | h3017
                      · linarith only [h2645, h3017, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h3017, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1800, h2644, h3015, h3016, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2643, h2645, h3015, hc01, hlam, hphi, ht12, u2elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3022 | h3022
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3023 | h3023
            · linarith only [h2643, h2644, h3023, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3025 | h3025
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3026 | h3026
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3027 | h3027
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3028 | h3028
                    · linarith only [h2643, h2644, h3028, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h3028, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2643, h3027, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h2643, h2644, h3025, h3026, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3033 | h3033
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3034 | h3034
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3035 | h3035
                    · linarith only [h2644, h3035, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h3035, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2643, h3034, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h2644, h3022, h3033, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3040 | h3040
            · linarith only [h2643, h2644, h3040, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3042 | h3042
              · linarith only [h2643, h3022, h3042, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3044 | h3044
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3045 | h3045
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3046 | h3046
                    · linarith only [h2644, h3046, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h3046, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2643, h3045, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3050 | h3050
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3051 | h3051
                    · linarith only [h2644, h3051, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h3051, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2643, h3050, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3055 | h3055
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3056 | h3056
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3057 | h3057
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3058 | h3058
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3059 | h3059
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3060 | h3060
                  · linarith only [h2643, h3060, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h3060, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3063 | h3063
                  · linarith only [h2643, h3055, h3063, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h3063, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2643, h3056, h3058, hlam]
            · linarith only [h2643, h3055, h3057, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3068 | h3068
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3069 | h3069
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3070 | h3070
                · linarith only [h3055, h3056, h3070, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3072 | h3072
                  · linarith only [h2643, h3055, h3072, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h3072, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3075 | h3075
                · linarith only [h2643, h3055, h3069, h3075, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3077 | h3077
                  · linarith only [h2643, h3055, h3077, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h3077, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h2643, h3055, h3068, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3081 | h3081
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3082 | h3082
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3083 | h3083
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3084 | h3084
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3085 | h3085
                  · linarith only [h2643, h3085, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h3085, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h3055, h3081, h3084, hlam]
              · linarith only [h2643, h3081, h3083, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3090 | h3090
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3091 | h3091
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3092 | h3092
                  · linarith only [h2512, h2643, h3081, h3092, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3092, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2643, h3081, h3082, h3091, hlam]
              · linarith only [h2643, h3081, h3090, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3097 | h3097
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3098 | h3098
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3099 | h3099
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3100 | h3100
                  · linarith only [h2643, h3100, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h3100, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3103 | h3103
                  · linarith only [h0, h2643, h3103, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3103, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3106 | h3106
                · linarith only [h3097, h3098, h3106, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3108 | h3108
                  · linarith only [h0, h2643, h3108, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3108, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3111 | h3111
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3112 | h3112
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3113 | h3113
                  · linarith only [h0, h2643, h3113, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3113, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h3097, h3111, h3112, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3117 | h3117
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3118 | h3118
                  · linarith only [h0, h2643, h3118, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3118, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3121 | h3121
                  · linarith only [h0, h2643, h3121, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3121, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h1800 | h1800
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x1_x0 m hb0 hb2 hb3 hb5 h0 h1800
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x1_x1 m hb0 hb2 hb3 hb5 h0 h1800

set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
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
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
