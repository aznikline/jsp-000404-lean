import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5224000 in
theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg811 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1501 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1980 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2294 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h811 := hg811
  rcases m.htr 0 2 4 (by decide) (by decide) with h2295 | h2295
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2296 | h2296
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2297 | h2297
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2298 | h2298
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2299 | h2299
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2300 | h2300
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2301 | h2301
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2302 | h2302
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2303 | h2303
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2304 | h2304
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2305 | h2305
                      · linarith only [h2294, h2305, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h2296, h2305, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2298, h2304, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h2296, h2297, h2303, h811, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                · linarith only [h2296, h2302, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2311 | h2311
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2312 | h2312
                  · linarith only [h2299, h2301, h2312, hlam]
                  · linarith only [h2294, h2297, h2312, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h2296, h2311, h811, hlam]
            · linarith only [h0, h2295, h2300, hlam]
          · linarith only [h0, h2294, h2299, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2318 | h2318
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2319 | h2319
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2320 | h2320
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2321 | h2321
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2322 | h2322
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2323 | h2323
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2324 | h2324
                      · linarith only [h2294, h2324, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h2294, h2296, h2324, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2327 | h2327
                      · linarith only [h2294, h2327, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h2296, h2327, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h2297, h2322, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                · linarith only [h2296, h2297, h2321, h811, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2332 | h2332
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2333 | h2333
                  · linarith only [h2318, h2320, h2333, hlam]
                  · linarith only [h1501, h2297, h2332, h2333, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2296, h2332, h811, hlam]
            · linarith only [h0, h2295, h2319, hlam]
          · linarith only [h0, h2294, h2318, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2339 | h2339
        · linarith only [h2296, h2297, h2339, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2341 | h2341
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2342 | h2342
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2343 | h2343
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2344 | h2344
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2345 | h2345
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2346 | h2346
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2347 | h2347
                      · linarith only [h2294, h2347, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h2296, h2347, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2350 | h2350
                      · linarith only [h2294, h2350, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h2296, h2297, h2341, h2345, h2350, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2353 | h2353
                    · linarith only [h1501, h2339, h2344, h2345, h2353, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2355 | h2355
                      · linarith only [h2294, h2355, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h2296, h2355, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2294, h2296, h2344, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2359 | h2359
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2360 | h2360
                  · linarith only [h2296, h2297, h2341, h2343, h2360, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2362 | h2362
                    · linarith only [h1501, h2339, h2342, h2343, h2362, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2364 | h2364
                      · linarith only [h2294, h2364, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h2296, h2364, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2294, h2296, h2359, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2295, h2342, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h2294, h2341, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2370 | h2370
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2371 | h2371
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2372 | h2372
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2373 | h2373
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2374 | h2374
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2375 | h2375
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2376 | h2376
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2377 | h2377
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2378 | h2378
                      · linarith only [h2294, h2296, h2378, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2380 | h2380
                        · linarith only [h2295, h2378, h2380, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h2370, h2380, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2295, h2371, h2377, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h2296, h2370, h2375, h2376, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2385 | h2385
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2386 | h2386
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2387 | h2387
                      · linarith only [h1980, h2375, h2385, h2387, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2389 | h2389
                        · linarith only [h2295, h2387, h2389, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h2370, h2389, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2295, h2371, h2386, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h2370, h2385, h811, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2394 | h2394
                · linarith only [h2296, h2370, h2372, h2374, h2394, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2396 | h2396
                  · linarith only [h2372, h2374, h2396, hlam]
                  · linarith only [h2370, h2396, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h2295, h2373, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h2294, h2372, hlam]
        · linarith only [h2296, h2370, h2371, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2402 | h2402
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2403 | h2403
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2404 | h2404
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2405 | h2405
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2406 | h2406
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2407 | h2407
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2408 | h2408
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2409 | h2409
                      · linarith only [h2294, h2296, h2409, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2411 | h2411
                        · linarith only [h2294, h2370, h2411, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2413 | h2413
                          · linarith only [h2295, h2413, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h2402, h2413, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h2296, h2402, h2406, h2408, hlam]
                  · linarith only [h2296, h2406, h2407, h811, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2418 | h2418
                  · linarith only [h2370, h2406, h2418, h811, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2420 | h2420
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2421 | h2421
                      · linarith only [h2294, h2370, h2406, h2421, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2423 | h2423
                        · linarith only [h2295, h2418, h2421, h2423, h811, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2425 | h2425
                          · linarith only [h2295, h2425, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h2295, h2402, h2425, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1501, h2402, h2420, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2429 | h2429
                · linarith only [h2296, h2403, h2405, h2429, h811, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2431 | h2431
                  · linarith only [h2370, h2429, h2431, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2433 | h2433
                    · linarith only [h2404, h2405, h2433, hlam]
                    · linarith only [h2295, h2402, h2429, h2433, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2295, h2404, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h2294, h2295, h2403, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2438 | h2438
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2439 | h2439
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2440 | h2440
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2441 | h2441
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2442 | h2442
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2443 | h2443
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2444 | h2444
                      · linarith only [h2294, h2296, h2444, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2446 | h2446
                        · linarith only [h2295, h2370, h2444, h2446, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2448 | h2448
                          · linarith only [h2295, h2402, h2448, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2450 | h2450
                            · linarith only [h2296, h2402, h2438, h2441, h2450, h811, hc01, hc12, hlam, hphi]
                            · linarith only [h2296, h2443, h2450, h811, hc01, hc14, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2453 | h2453
                      · linarith only [h2294, h2296, h2453, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2455 | h2455
                        · linarith only [h2294, h2370, h2455, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2457 | h2457
                          · linarith only [h2295, h2443, h2457, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2459 | h2459
                            · linarith only [h2441, h2443, h2459, hlam]
                            · rcases h1bigk with h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [hlam, p2461_0]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h0, hlam, p2461_0]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h811, hlam, p2461_0]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h1501, hlam, p2461_0]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h1980, hlam, p2461_0]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                rcases p2461_3 (m.d 0 1) (by simp) with h2467 | h2467
                                · linarith only [h2467, hlam, p2461_0]
                                · rcases p2461_3 (m.d 1 2) (by simp) with h2469 | h2469
                                  · rcases p2461_3 (m.d 1 3) (by simp) with h2470 | h2470
                                    · linarith only [h2438, h2470, hlam]
                                    · linarith only [h2470, h811, hlam]
                                  · linarith only [h2469, hlam, p2461_0]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [hlam, p2461_0]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h811, hc01, hc12, hlam, hphi, p2461_1]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h2296, h2441, h811, hc01, hc12, hlam, hphi, p2461_1]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h1980, hc01, hc12, hlam, hphi, p2461_1]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                rcases p2461_3 (m.d 0 1) (by simp) with h2478 | h2478
                                · linarith only [h2478, hlam, p2461_0]
                                · rcases p2461_3 (m.d 1 2) (by simp) with h2480 | h2480
                                  · rcases p2461_3 (m.d 1 3) (by simp) with h2481 | h2481
                                    · rcases p2461_3 (m.d 1 4) (by simp) with h2482 | h2482
                                      · linarith only [h2441, h2482, hlam]
                                      · linarith only [h1501, h2482, hlam]
                                    · linarith only [h2481, hlam, p2461_0]
                                  · linarith only [h0, h2480, hlam]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h2438, hlam, p2461_1]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [hlam, p2461_0]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h2296, h2441, h811, hc01, hc13, hlam, hphi, p2461_1]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h2296, h2438, h2442, h2459, h811, hc01, hc12, hlam, hphi, p2461_1]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h2443, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2461_1]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h2439, hlam, p2461_1]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h2441, hlam, p2461_0]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [hlam, p2461_0]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h2443, hlam, p2461_1]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                rcases p2461_3 (m.d 0 1) (by simp) with h2496 | h2496
                                · linarith only [h2496, hlam, p2461_0]
                                · rcases p2461_3 (m.d 1 2) (by simp) with h2498 | h2498
                                  · rcases p2461_3 (m.d 1 3) (by simp) with h2499 | h2499
                                    · rcases p2461_3 (m.d 1 4) (by simp) with h2500 | h2500
                                      · linarith only [h2443, h2500, hlam]
                                      · linarith only [h1501, h2500, hlam]
                                    · linarith only [h2499, h811, hlam]
                                  · linarith only [h0, h2498, hlam]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h2440, hlam, p2461_1]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h2442, hlam, p2461_0]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [h1501, hc01, hc15, hlam, hphi, p2461_1]
                              · have p2461_0 := h2461c.1
                                have p2461_1 := h2461c.2.1
                                have p2461_2 := h2461c.2.2.1
                                have p2461_3 := h2461c.2.2.2
                                linarith only [hlam, p2461_0]
                  · linarith only [h2296, h2441, h2442, h811, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2510 | h2510
                  · linarith only [h2370, h2441, h2510, h811, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2512 | h2512
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2513 | h2513
                      · linarith only [h2441, h2513, h811, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2515 | h2515
                        · linarith only [h2295, h2513, h2515, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2517 | h2517
                          · linarith only [h2295, h2296, h2402, h2517, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2519 | h2519
                            · rcases h1bigk with h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c | h2520c
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [hlam, p2520_0]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h0, hlam, p2520_0]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h811, hlam, p2520_0]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h1501, hlam, p2520_0]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h1980, hlam, p2520_0]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                rcases p2520_3 (m.d 0 1) (by simp) with h2526 | h2526
                                · linarith only [h2526, hlam, p2520_0]
                                · rcases p2520_3 (m.d 1 2) (by simp) with h2528 | h2528
                                  · rcases p2520_3 (m.d 1 3) (by simp) with h2529 | h2529
                                    · linarith only [h2438, h2529, hlam]
                                    · linarith only [h2529, h811, hlam]
                                  · linarith only [h2528, hlam, p2520_0]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [hlam, p2520_0]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h811, hc01, hc12, hlam, hphi, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h2296, h2402, h2512, h811, hc01, hc12, hlam, hphi, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h2296, h2402, h2512, h811, hc01, hc12, hlam, hphi, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h2510, hc01, hc35, hlam, hphi, ht12, ht23, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h2438, hlam, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [hlam, p2520_0]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h2441, hlam, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h2510, hlam, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                rcases p2520_3 (m.d 0 1) (by simp) with h2542 | h2542
                                · linarith only [h2542, hlam, p2520_0]
                                · rcases p2520_3 (m.d 1 2) (by simp) with h2544 | h2544
                                  · rcases p2520_3 (m.d 1 3) (by simp) with h2545 | h2545
                                    · linarith only [h2441, h2545, hlam]
                                    · linarith only [h2545, h811, hlam]
                                  · linarith only [h0, h2544, hlam]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h2439, hlam, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h811, hc01, hc14, hlam, hphi, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [hlam, p2520_0]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h2441, h2510, h811, hc01, hc34, hlam, hphi, ht12, ht23, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                rcases p2520_3 (m.d 0 1) (by simp) with h2553 | h2553
                                · linarith only [h2553, hlam, p2520_0]
                                · rcases p2520_3 (m.d 1 2) (by simp) with h2555 | h2555
                                  · rcases p2520_3 (m.d 1 3) (by simp) with h2556 | h2556
                                    · linarith only [h2510, h2556, hlam]
                                    · linarith only [h2556, h811, hlam]
                                  · linarith only [h0, h2555, hlam]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h2440, hlam, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h811, hc01, hc15, hlam, hphi, p2520_1]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [h2512, hlam, p2520_0]
                              · have p2520_0 := h2520c.1
                                have p2520_1 := h2520c.2.1
                                have p2520_2 := h2520c.2.2.1
                                have p2520_3 := h2520c.2.2.2
                                linarith only [hlam, p2520_0]
                            · linarith only [h2441, h2519, h811, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2565 | h2565
                      · linarith only [h2294, h2441, h2565, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2567 | h2567
                        · linarith only [h2295, h2565, h2567, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2569 | h2569
                          · linarith only [h2295, h2569, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2571 | h2571
                            · linarith only [h1501, h2512, h2571, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h2441, h2571, h811, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2574 | h2574
                · linarith only [h2296, h2438, h2440, h2574, h811, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2576 | h2576
                  · linarith only [h2370, h2438, h2440, h2576, h811, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2578 | h2578
                    · linarith only [h1501, h2402, h2439, h2440, h2578, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2580 | h2580
                      · linarith only [h2294, h2580, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2582 | h2582
                        · linarith only [h2295, h2576, h2580, h2582, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2584 | h2584
                          · linarith only [h2295, h2578, h2584, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2586 | h2586
                            · linarith only [h0, h2440, h2584, h2586, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h2574, h2586, h811, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h2295, h2439, hlam]
          · linarith only [h0, h2294, h2438, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2591 | h2591
    · linarith only [h2294, h2295, h2591, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2593 | h2593
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2594 | h2594
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2595 | h2595
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2596 | h2596
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2597 | h2597
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2598 | h2598
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2599 | h2599
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2600 | h2600
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2601 | h2601
                      · linarith only [h1980, h2294, h2591, h2593, h2601, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2603 | h2603
                        · linarith only [h2294, h2295, h2595, h2598, h2601, h2603, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h2294, h2295, h2593, h2595, h2598, h2601, h2603, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2594, h2600, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h2591, h2593, h2598, h2599, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2608 | h2608
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2609 | h2609
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2610 | h2610
                      · linarith only [h2294, h2598, h2610, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2612 | h2612
                        · linarith only [h2294, h2295, h2596, h2612, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h2593, h2612, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2295, h2594, h2596, h2609, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h2294, h2593, h2608, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1980, h2294, h2295, h2593, h2596, h2597, hc01, hc25, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2618 | h2618
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2619 | h2619
                · linarith only [h1980, h2591, h2593, h2595, h2596, h2619, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2621 | h2621
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2622 | h2622
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2623 | h2623
                      · linarith only [h1980, h2294, h2619, h2621, h2623, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2625 | h2625
                        · linarith only [h2294, h2295, h2625, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h2294, h2295, h2593, h2625, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h2594, h2596, h2622, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h2593, h2621, h811, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2630 | h2630
                · linarith only [h2591, h2593, h2595, h2618, h2630, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2632 | h2632
                  · linarith only [h2595, h2618, h2632, hlam]
                  · linarith only [h2593, h2632, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
          · linarith only [h0, h2294, h2595, hlam]
        · linarith only [h2294, h2295, h2593, h2594, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2637 | h2637
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2638 | h2638
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2639 | h2639
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2640 | h2640
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2641 | h2641
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2642 | h2642
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2643 | h2643
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2644 | h2644
                      · linarith only [h2294, h2295, h2591, h2644, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2646 | h2646
                        · linarith only [h2294, h2295, h2593, h2638, h2641, h2644, h2646, h811, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2648 | h2648
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2649 | h2649
                            · rcases h1bigk with h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c | h2650c
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h0, hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h811, hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h1501, hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h1980, hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                rcases p2650_3 (m.d 0 1) (by simp) with h2656 | h2656
                                · linarith only [h2656, hlam, p2650_0]
                                · rcases p2650_3 (m.d 1 2) (by simp) with h2658 | h2658
                                  · rcases p2650_3 (m.d 1 3) (by simp) with h2659 | h2659
                                    · linarith only [h2638, h2659, hlam]
                                    · linarith only [h2659, h811, hlam]
                                  · linarith only [h2658, hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2295, h2641, h2644, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2650_1]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2294, h2295, h2641, h2644, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2650_1]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2593, h2642, h811, hc01, hc12, hlam, hphi, p2650_1]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                rcases p2650_3 (m.d 0 1) (by simp) with h2667 | h2667
                                · linarith only [h2667, hlam, p2650_0]
                                · rcases p2650_3 (m.d 1 2) (by simp) with h2669 | h2669
                                  · rcases p2650_3 (m.d 1 3) (by simp) with h2670 | h2670
                                    · rcases p2650_3 (m.d 1 4) (by simp) with h2671 | h2671
                                      · linarith only [h2641, h2671, hlam]
                                      · linarith only [h1501, h2671, hlam]
                                    · linarith only [h2670, hlam, p2650_0]
                                  · linarith only [h0, h2669, hlam]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2638, hlam, p2650_1]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2294, h2295, h2641, h2644, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2650_1]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2593, h2638, h2642, h811, hc01, hc12, hlam, hphi, p2650_1]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                rcases p2650_3 (m.d 0 1) (by simp) with h2680 | h2680
                                · linarith only [h2680, hlam, p2650_0]
                                · rcases p2650_3 (m.d 1 2) (by simp) with h2682 | h2682
                                  · rcases p2650_3 (m.d 1 3) (by simp) with h2683 | h2683
                                    · rcases p2650_3 (m.d 1 4) (by simp) with h2684 | h2684
                                      · rcases p2650_3 (m.d 1 5) (by simp) with h2685 | h2685
                                        · linarith only [h2643, h2685, hlam]
                                        · linarith only [h1980, h2685, hlam]
                                      · linarith only [h2684, hlam, p2650_0]
                                    · linarith only [h2683, h811, hlam]
                                  · linarith only [h0, h2682, hlam]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2639, hlam, p2650_1]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2641, hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2593, h2642, h811, hc01, hc14, hlam, hphi, p2650_1]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                rcases p2650_3 (m.d 0 1) (by simp) with h2695 | h2695
                                · linarith only [h2695, hlam, p2650_0]
                                · rcases p2650_3 (m.d 1 2) (by simp) with h2697 | h2697
                                  · rcases p2650_3 (m.d 1 3) (by simp) with h2698 | h2698
                                    · rcases p2650_3 (m.d 1 4) (by simp) with h2699 | h2699
                                      · rcases p2650_3 (m.d 1 5) (by simp) with h2700 | h2700
                                        · rcases h3bigk with h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c | h2701c
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h811, hlam, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2701_1, u0elo2]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2591, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2593, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            rcases p2701_3 (m.d 0 3) (by simp) with h2707 | h2707
                                            · linarith only [h2707, h811, hlam]
                                            · rcases p2701_3 (m.d 1 3) (by simp) with h2709 | h2709
                                              · rcases p2701_3 (m.d 2 3) (by simp) with h2710 | h2710
                                                · linarith only [h2638, h2710, hlam]
                                                · rcases p2701_3 (m.d 3 4) (by simp) with h2712 | h2712
                                                  · linarith only [h2641, h2712, hlam]
                                                  · linarith only [h2591, h2712, hlam]
                                              · linarith only [h2709, h811, hlam]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2294, h2295, h2641, h2644, hlam, p2701_2]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2294, h2295, h2644, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2593, h2638, h811, hc01, hc12, hlam, hphi, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2294, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2638, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2644, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2646, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2638, h2641, h811, hc01, hc12, hlam, hphi, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2641, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            rcases p2701_3 (m.d 0 3) (by simp) with h2727 | h2727
                                            · linarith only [h2591, h2727, hlam]
                                            · linarith only [h2294, h2727, hlam]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2593, h2638, h2641, h811, hc01, hc12, hlam, hphi, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2638, h2642, h811, hc01, hc12, hlam, hphi, p2701_1]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2642, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            rcases p2701_3 (m.d 0 3) (by simp) with h2734 | h2734
                                            · linarith only [h2593, h2734, hlam]
                                            · linarith only [h2294, h2734, hlam]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [h2649, hlam, p2701_0]
                                          · have p2701_0 := h2701c.1
                                            have p2701_1 := h2701c.2.1
                                            have p2701_2 := h2701c.2.2.1
                                            have p2701_3 := h2701c.2.2.2
                                            linarith only [hlam, p2701_0]
                                        · linarith only [h2700, hlam, p2650_0]
                                      · linarith only [h1501, h2699, hlam]
                                    · linarith only [h2698, h811, hlam]
                                  · linarith only [h0, h2697, hlam]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2640, hlam, p2650_1]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2642, hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [h2643, hlam, p2650_0]
                              · have p2650_0 := h2650c.1
                                have p2650_1 := h2650c.2.1
                                have p2650_2 := h2650c.2.2.1
                                have p2650_3 := h2650c.2.2.2
                                linarith only [hlam, p2650_0]
                            · linarith only [h2637, h2649, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h2294, h2295, h2637, h2648, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h2637, h2643, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h2591, h2641, h2642, h811, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2751 | h2751
                  · linarith only [h2593, h2641, h2751, h811, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2753 | h2753
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2754 | h2754
                      · linarith only [h2294, h2641, h2754, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2756 | h2756
                        · linarith only [h2294, h2295, h2639, h2751, h2756, h811, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2758 | h2758
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2759 | h2759
                            · rcases h1bigk with h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [hlam, p2760_0]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h0, hlam, p2760_0]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h811, hlam, p2760_0]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h1501, hlam, p2760_0]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h1980, hlam, p2760_0]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                rcases p2760_3 (m.d 0 1) (by simp) with h2766 | h2766
                                · linarith only [h2766, hlam, p2760_0]
                                · rcases p2760_3 (m.d 1 2) (by simp) with h2768 | h2768
                                  · rcases p2760_3 (m.d 1 3) (by simp) with h2769 | h2769
                                    · linarith only [h2638, h2769, hlam]
                                    · linarith only [h2769, h811, hlam]
                                  · linarith only [h2768, hlam, p2760_0]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [hlam, p2760_0]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h811, hc01, hc12, hlam, hphi, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h2294, h2295, h2639, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h1980, hc01, hc12, hlam, hphi, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h2751, hc01, hc35, hlam, hphi, ht12, ht23, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h2638, hlam, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [hlam, p2760_0]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h2641, hlam, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h2751, hlam, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                rcases p2760_3 (m.d 0 1) (by simp) with h2782 | h2782
                                · linarith only [h2782, hlam, p2760_0]
                                · rcases p2760_3 (m.d 1 2) (by simp) with h2784 | h2784
                                  · rcases p2760_3 (m.d 1 3) (by simp) with h2785 | h2785
                                    · linarith only [h2641, h2785, hlam]
                                    · linarith only [h2785, h811, hlam]
                                  · linarith only [h0, h2784, hlam]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h2639, hlam, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h811, hc01, hc14, hlam, hphi, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [hlam, p2760_0]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h2641, h2751, h811, hc01, hc34, hlam, hphi, ht12, ht23, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                rcases p2760_3 (m.d 0 1) (by simp) with h2793 | h2793
                                · linarith only [h2793, hlam, p2760_0]
                                · rcases p2760_3 (m.d 1 2) (by simp) with h2795 | h2795
                                  · rcases p2760_3 (m.d 1 3) (by simp) with h2796 | h2796
                                    · linarith only [h2751, h2796, hlam]
                                    · linarith only [h2796, h811, hlam]
                                  · linarith only [h0, h2795, hlam]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h2640, hlam, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h811, hc01, hc15, hlam, hphi, p2760_1]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [h2753, hlam, p2760_0]
                              · have p2760_0 := h2760c.1
                                have p2760_1 := h2760c.2.1
                                have p2760_2 := h2760c.2.2.1
                                have p2760_3 := h2760c.2.2.2
                                linarith only [hlam, p2760_0]
                            · linarith only [h2637, h2641, h2759, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h2294, h2295, h2637, h2758, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h2294, h2295, h2637, h2639, h2753, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
              · linarith only [h2294, h2295, h2639, h2640, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2808 | h2808
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2809 | h2809
                · linarith only [h2591, h2638, h2639, h2809, h811, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2811 | h2811
                  · linarith only [h2593, h2809, h2811, h811, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2813 | h2813
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2814 | h2814
                      · linarith only [h2294, h2814, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2816 | h2816
                        · linarith only [h2294, h2295, h2811, h2816, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2818 | h2818
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2819 | h2819
                            · rcases h1bigk with h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [hlam, p2820_0]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h0, hlam, p2820_0]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h811, hlam, p2820_0]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h1501, hlam, p2820_0]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h1980, hlam, p2820_0]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2639, h2814, hc01, hc34, hlam, hphi, ht12, ht23, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [hlam, p2820_0]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2639, h2814, h811, hc01, hc34, hlam, hphi, ht12, ht23, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2639, hlam, p2820_0]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h1980, h2639, h2814, hc01, hc34, hlam, hphi, ht12, ht23, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2811, hc01, hc35, hlam, hphi, ht12, ht23, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2638, hlam, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [hlam, p2820_0]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2809, hlam, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2811, hlam, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                rcases p2820_3 (m.d 0 1) (by simp) with h2836 | h2836
                                · linarith only [h2836, hlam, p2820_0]
                                · rcases p2820_3 (m.d 1 2) (by simp) with h2838 | h2838
                                  · linarith only [h2639, h2838, hlam]
                                  · linarith only [h0, h2838, hlam]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2639, h2814, h811, hc01, hc34, hlam, hphi, ht12, ht23, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [hlam, p2820_0]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2639, h2811, h2814, h811, hc01, hc34, hlam, hphi, ht12, ht23, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2639, h2808, h2814, hc01, hc34, hlam, hphi, ht12, ht23, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2808, hlam, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2639, h2808, h2814, h811, hc01, hc34, hlam, hphi, ht12, ht23, p2820_1]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [h2813, hlam, p2820_0]
                              · have p2820_0 := h2820c.1
                                have p2820_1 := h2820c.2.1
                                have p2820_2 := h2820c.2.2.1
                                have p2820_3 := h2820c.2.2.2
                                linarith only [hlam, p2820_0]
                            · linarith only [h2637, h2639, h2814, h2819, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h2637, h2639, h2808, h2811, h2818, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h2637, h2813, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2853 | h2853
                · linarith only [h2591, h2638, h2639, h2853, h811, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2855 | h2855
                  · linarith only [h2593, h2853, h2855, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2857 | h2857
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2858 | h2858
                      · linarith only [h2294, h2295, h2853, h2858, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2860 | h2860
                        · linarith only [h2294, h2295, h2855, h2860, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2862 | h2862
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2863 | h2863
                            · rcases h1bigk with h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c | h2864c
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [hlam, p2864_0]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h0, hlam, p2864_0]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h811, hlam, p2864_0]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h1501, hlam, p2864_0]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h1980, hlam, p2864_0]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2808, h2858, h2862, hc01, hc34, hlam, hphi, ht12, ht23, p2864_1]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [hlam, p2864_0]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2808, h2858, h2862, h811, hc01, hc34, hlam, hphi, ht12, ht23, p2864_1]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2639, hlam, p2864_0]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2808, hlam, p2864_0]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2638, h2808, h2858, h2862, hc01, hc34, hlam, hphi, ht12, ht23, p2864_1]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2638, hlam, p2864_1]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [hlam, p2864_0]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2853, hlam, p2864_1]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2855, hlam, p2864_1]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                rcases p2864_3 (m.d 0 1) (by simp) with h2880 | h2880
                                · linarith only [h2880, hlam, p2864_0]
                                · rcases p2864_3 (m.d 1 2) (by simp) with h2882 | h2882
                                  · linarith only [h2639, h2882, hlam]
                                  · linarith only [h0, h2882, hlam]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p2864_1]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2639, h2858, h811, hc01, hc34, hlam, hphi, ht12, ht23, p2864_1]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [hlam, p2864_0]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2638, h2639, h2808, h2858, h811, hc01, hc34, hlam, hphi, ht12, ht23, p2864_1]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                rcases p2864_3 (m.d 0 1) (by simp) with h2889 | h2889
                                · linarith only [h2889, hlam, p2864_0]
                                · rcases p2864_3 (m.d 1 2) (by simp) with h2891 | h2891
                                  · linarith only [h2808, h2891, hlam]
                                  · linarith only [h0, h2891, hlam]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2638, h811, hc01, hc15, hlam, hphi, p2864_1]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2808, h2858, h2862, h811, hc01, hc34, hlam, hphi, ht12, ht23, p2864_1]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [h2857, hlam, p2864_0]
                              · have p2864_0 := h2864c.1
                                have p2864_1 := h2864c.2.1
                                have p2864_2 := h2864c.2.2.1
                                have p2864_3 := h2864c.2.2.2
                                linarith only [hlam, p2864_0]
                            · linarith only [h1501, h2637, h2639, h2858, h2863, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                          · linarith only [h2637, h2638, h2639, h2862, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h2637, h2857, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
          · linarith only [h0, h2294, h2638, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2902 | h2902
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2903 | h2903
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2904 | h2904
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2905 | h2905
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2906 | h2906
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2907 | h2907
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2908 | h2908
                      · linarith only [h2294, h2295, h2591, h2637, h2902, h2905, h2907, h2908, h811, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2910 | h2910
                        · linarith only [h2294, h2295, h2593, h2637, h2902, h2905, h2907, h2910, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2912 | h2912
                          · linarith only [h2294, h2295, h2637, h2908, h2912, hc23, hc34, hlam, hphi]
                          · linarith only [h2294, h2295, h2902, h2905, h2907, h2912, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2294, h2295, h2903, h2907, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h2591, h2905, h2906, h811, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2917 | h2917
                  · linarith only [h2593, h2905, h2917, h811, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2919 | h2919
                    · linarith only [h2294, h2295, h2637, h2905, h2919, hc23, hc34, hlam, hphi]
                    · linarith only [h2294, h2295, h2903, h2919, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h2294, h2295, h2903, h2904, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2923 | h2923
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2924 | h2924
                · linarith only [h2591, h2902, h2903, h2924, h811, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2926 | h2926
                  · linarith only [h2593, h2924, h2926, h811, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2928 | h2928
                    · linarith only [h2294, h2295, h2637, h2924, h2928, hc23, hc34, hlam, hphi]
                    · linarith only [h2903, h2923, h2928, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2931 | h2931
                · linarith only [h2591, h2902, h2923, h2931, h811, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2933 | h2933
                  · linarith only [h2593, h2931, h2933, h811, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2935 | h2935
                    · linarith only [h2294, h2295, h2637, h2931, h2935, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2937 | h2937
                      · linarith only [h2294, h2937, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2939 | h2939
                        · linarith only [h2294, h2933, h2939, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2941 | h2941
                          · linarith only [h0, h2903, h2935, h2937, h2941, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h2294, h2295, h2941, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h2294, h2902, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]

end R2N4
