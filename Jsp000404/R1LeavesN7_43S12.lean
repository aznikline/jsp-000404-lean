import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_43S10
import Jsp000404.R1LeavesN7_43S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1479 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2008 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2372 | h2372
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2373 | h2373
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2374 | h2374
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2375 | h2375
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2376 | h2376
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2377 | h2377
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2378 | h2378
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2379 | h2379
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2380 | h2380
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2381 | h2381
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2382 | h2382
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2383 | h2383
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2384 | h2384
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2385 | h2385
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2386 | h2386
                              · rcases h0bigk with h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c | h2387c
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [hlam, p2387_0]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h0, hlam, p2387_1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h1479, hlam, p2387_0]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h2008, hlam, p2387_1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h2008, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p2387_1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2387_1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [hlam, p2387_0]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h0, h2373, h2383, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2387_1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h0, h2008, h2372, h2380, h2384, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2387_1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  rcases p2387_3 (m.d 0 1) (by simp) with h2397 | h2397
                                  · linarith only [h0, h2397, hlam]
                                  · linarith only [h2372, h2397, hlam]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h2372, h2380, h2384, h2386, hc03, hc45, hlam, hphi, ht0b, ht5b, p2387_1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h2373, hlam, p2387_1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [hlam, p2387_0]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h1479, h2008, h2372, h2380, h2384, h2386, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2387_1, u3elo1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h1479, h2372, h2380, h2384, h2386, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2387_1, u3elo1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h2372, h2380, h2384, h2386, hc04, hc45, hlam, hphi, ht0b, ht5b, p2387_1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h2374, hlam, p2387_0]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h2376, hlam, p2387_0]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [hlam, p2387_0]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h1479, h2372, h2376, h2380, h2384, h2386, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2387_1, u3elo1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h2372, hlam, p2387_0]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h2375, hlam, p2387_1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h2377, hlam, p2387_0]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [h2378, hlam, p2387_1]
                                · have p2387_0 := h2387c.1
                                  have p2387_1 := h2387c.2.1
                                  have p2387_2 := h2387c.2.2.1
                                  have p2387_3 := h2387c.2.2.2
                                  linarith only [hlam, p2387_0]
                              · linarith only [h2008, h2372, h2381, h2382, h2386, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h2008, h2372, h2381, h2382, h2385, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1479, h2377, h2383, h2384, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h1479, h2376, h2383, hc23, hlam, hphi, u3elo1]
                      · linarith only [h2008, h2372, h2378, h2382, hc04, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1479, h2372, h2376, h2380, h2381, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h2375, h2380, hlam]
                · linarith only [h0, h2379, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h2008, h2372, h2378, hlam]
            · linarith only [h1479, h2372, h2377, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2425 | h2425
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2426 | h2426
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2427 | h2427
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2428 | h2428
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2429 | h2429
                    · linarith only [h1479, h2376, h2429, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1479, h2372, h2428, h2429, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h1479, h2372, h2375, h2427, h2428, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h2372, h2427, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h2008, h2372, h2426, hlam]
            · linarith only [h1479, h2372, h2425, hlam]
        · linarith only [h1479, h2372, h2373, h2375, hc23, hlam, hphi, u3elo1]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2437 | h2437
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2438 | h2438
          · linarith only [h2373, h2374, h2438, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2440 | h2440
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2441 | h2441
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2442 | h2442
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2443 | h2443
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2444 | h2444
                    · linarith only [h1479, h2372, h2438, h2443, h2444, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h1479, h2372, h2443, h2444, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h2374, h2437, h2443, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2373, h2442, hlam]
              · linarith only [h1479, h2372, h2373, h2374, h2441, hc23, hlam, hphi, u3elo1]
            · linarith only [h1479, h2372, h2440, hlam]
        · linarith only [h0, h2372, h2437, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2452 | h2452
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2453 | h2453
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2454 | h2454
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2455 | h2455
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2456 | h2456
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2457 | h2457
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2458 | h2458
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2459 | h2459
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2460 | h2460
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2461 | h2461
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2462 | h2462
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2463 | h2463
                            · linarith only [h2373, h2452, h2457, h2463, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h2373, h2452, h2456, h2457, h2461, h2463, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h2008, h2373, h2452, h2462, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h2008, h2372, h2373, h2452, h2458, h2461, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h2373, h2452, h2456, h2457, h2460, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2373, h2452, h2454, h2457, h2459, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h2373, h2453, h2457, h2458, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h0, h2372, h2457, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h2008, h2372, h2456, hlam]
            · linarith only [h1479, h2372, h2455, hlam]
          · linarith only [h2373, h2452, h2454, hlam]
        · linarith only [h2008, h2372, h2452, h2453, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2476 | h2476
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2477 | h2477
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2478 | h2478
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2479 | h2479
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2480 | h2480
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2481 | h2481
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2482 | h2482
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2483 | h2483
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2484 | h2484
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2485 | h2485
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2486 | h2486
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2487 | h2487
                              · rcases h0bigk with h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c | h2488c
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [hlam, p2488_0]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h0, hlam, p2488_1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h1479, hlam, p2488_0]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2008, hlam, p2488_1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2008, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p2488_1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2372, h2452, hc04, hc15, hlam, hphi, ht0b, ht5b, p2488_1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [hlam, p2488_0]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2373, hlam, p2488_0]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2452, hlam, p2488_1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2372, h2373, h2480, h2481, h2485, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2488_1, u3elo1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2372, h2481, h2485, hc03, hc35, hlam, hphi, ht0b, ht5b, p2488_1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2373, h2480, hc02, hlam, hphi, ht23, p2488_1, u3elo1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [hlam, p2488_0]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2373, h2480, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2488_1, u3elo1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2372, h2373, h2480, h2481, h2485, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2488_1, u3elo1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2372, h2481, h2485, hc04, hc35, hlam, hphi, ht0b, ht5b, p2488_1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h0, h2372, h2452, h2481, h2485, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2488_1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2477, hlam, p2488_0]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [hlam, p2488_0]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2372, h2373, h2477, h2480, h2481, h2485, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2488_1, u3elo1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2372, hlam, p2488_0]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2476, hlam, p2488_1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2478, hlam, p2488_0]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [h2479, hlam, p2488_1]
                                · have p2488_0 := h2488c.1
                                  have p2488_1 := h2488c.2.1
                                  have p2488_2 := h2488c.2.2.1
                                  have p2488_3 := h2488c.2.2.2
                                  linarith only [hlam, p2488_0]
                              · linarith only [h1479, h2372, h2483, h2487, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h0, h2372, h2452, h2483, h2486, hlam]
                          · linarith only [h0, h2452, h2484, h2485, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h2372, h2373, h2483, h2484, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h2008, h2372, h2477, h2479, h2483, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2373, h2477, h2480, h2482, hlam]
                  · linarith only [h0, h2372, h2476, h2481, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h2372, h2480, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h2008, h2372, h2479, hlam]
            · linarith only [h0, h2372, h2452, h2477, h2478, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2524 | h2524
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2525 | h2525
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2526 | h2526
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2527 | h2527
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2528 | h2528
                    · linarith only [h2477, h2528, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1479, h2372, h2527, h2528, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h2373, h2526, h2527, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h2372, h2526, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h0, h2372, h2373, h2477, h2525, hlam]
            · linarith only [h0, h2372, h2373, h2524, hlam]
        · linarith only [h0, h2372, h2476, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2536 | h2536
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2537 | h2537
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2538 | h2538
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2539 | h2539
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2540 | h2540
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2541 | h2541
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2542 | h2542
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2543 | h2543
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2544 | h2544
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2545 | h2545
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2546 | h2546
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2547 | h2547
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2548 | h2548
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2549 | h2549
                              · rcases h0bigk with h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [hlam, p2550_0]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h0, hlam, p2550_1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h1479, hlam, p2550_0]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h2008, hlam, p2550_1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h2372, hlam, p2550_1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2550_1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [hlam, p2550_0]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h0, h2536, h2546, h2549, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2550_1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h0, h2008, hc01, hc12, hlam, hphi, p2550_1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h0, h2372, hc01, hc12, hlam, hphi, p2550_1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p2550_1, u3elo0]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h2536, hlam, p2550_1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [hlam, p2550_0]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h1479, h2372, h2541, hc01, hlam, hphi, ht12, ht23, p2550_1, u3elo1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h1479, h2372, hc01, hlam, hphi, ht12, ht23, p2550_1, u3elo1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h2008, h2544, hc01, hlam, hphi, ht12, ht23, p2550_1, u3elo1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h2537, hlam, p2550_0]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h2539, hlam, p2550_0]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [hlam, p2550_0]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h2008, h2372, h2544, hc01, hlam, hphi, ht12, ht23, p2550_1, u3elo1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h2372, h2544, h2545, hc01, hlam, hphi, ht12, ht23, p2550_1, u3elo1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h2538, hlam, p2550_1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h2540, hlam, p2550_0]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [h2541, hlam, p2550_1]
                                · have p2550_0 := h2550c.1
                                  have p2550_1 := h2550c.2.1
                                  have p2550_2 := h2550c.2.2.1
                                  have p2550_3 := h2550c.2.2.2
                                  linarith only [hlam, p2550_0]
                              · rcases h0bigk with h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h0, hlam, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h1479, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2008, hlam, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2372, hlam, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h0, h2536, h2546, h2548, h2549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h0, h2008, hc01, hc12, hlam, hphi, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h0, h2372, hc01, hc12, hlam, hphi, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h1479, hc01, hlam, hphi, ht12, ht23, p2576_1, u3elo1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2536, hlam, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h1479, h2537, h2548, h2549, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2576_1, u3elo1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h1479, h2372, hc01, hlam, hphi, ht12, ht23, p2576_1, u3elo1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2008, h2544, hc01, hlam, hphi, ht12, ht23, p2576_1, u3elo1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2537, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2539, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2008, h2372, h2544, hc01, hlam, hphi, ht12, ht23, p2576_1, u3elo1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2372, h2544, h2545, hc01, hlam, hphi, ht12, ht23, p2576_1, u3elo1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2538, hlam, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2540, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2541, hlam, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [hlam, p2576_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2602 | h2602
                              · linarith only [h1479, h2539, h2548, h2602, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · rcases h0bigk with h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c | h2604c
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [hlam, p2604_0]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h0, hlam, p2604_1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h1479, hlam, p2604_0]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h2008, hlam, p2604_1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h2372, hlam, p2604_1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2604_1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [hlam, p2604_0]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h0, h1479, hc01, hc12, hlam, hphi, p2604_1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h0, h2008, hc01, hc12, hlam, hphi, p2604_1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h0, h2372, hc01, hc12, hlam, hphi, p2604_1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p2604_1, u3elo0]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h2536, hlam, p2604_1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [hlam, p2604_0]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h1479, h2008, hc01, hlam, hphi, ht12, ht23, p2604_1, u3elo1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h1479, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2604_1, u3elo1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h2008, h2544, hc01, hlam, hphi, ht12, ht23, p2604_1, u3elo1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h2537, hlam, p2604_0]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h2539, hlam, p2604_0]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [hlam, p2604_0]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h2008, h2372, h2544, hc01, hlam, hphi, ht12, ht23, p2604_1, u3elo1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h2372, h2544, h2545, hc01, hlam, hphi, ht12, ht23, p2604_1, u3elo1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h2538, hlam, p2604_1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h2540, hlam, p2604_0]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [h2541, hlam, p2604_1]
                                · have p2604_0 := h2604c.1
                                  have p2604_1 := h2604c.2.1
                                  have p2604_2 := h2604c.2.2.1
                                  have p2604_3 := h2604c.2.2.2
                                  linarith only [hlam, p2604_0]
                          · linarith only [h1479, h2540, h2547, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1479, h2539, h2546, hc23, hlam, hphi, u3elo1]
                      · linarith only [h2008, h2541, h2545, hlam]
                    · linarith only [h1479, h2539, h2544, hlam]
                  · linarith only [h0, h2538, h2543, hlam]
                · linarith only [h0, h2542, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2636 | h2636
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2637 | h2637
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2638 | h2638
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2639 | h2639
                      · linarith only [h2008, h2541, h2638, h2639, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2641 | h2641
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2642 | h2642
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2643 | h2643
                            · linarith only [h2008, h2639, h2643, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2645 | h2645
                              · linarith only [h2008, h2639, h2641, h2645, hc01, hc23, hlam, hphi, ht12]
                              · rcases h0bigk with h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [hlam, p2647_0]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h0, hlam, p2647_1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h1479, hlam, p2647_0]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h2008, hlam, p2647_1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h2372, hlam, p2647_1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2647_1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [hlam, p2647_0]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h0, h2536, h2642, h2645, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2647_1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h0, h2008, hc01, hc12, hlam, hphi, p2647_1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h0, h2372, hc01, hc12, hlam, hphi, p2647_1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p2647_1, u3elo0]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h2536, hlam, p2647_1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [hlam, p2647_0]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h1479, h2008, hc01, hlam, hphi, ht12, ht23, p2647_1, u3elo1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h1479, h2372, hc01, hlam, hphi, ht12, ht23, p2647_1, u3elo1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h2008, hc01, hc14, hlam, hphi, p2647_1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h2537, hlam, p2647_0]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h2539, hlam, p2647_0]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [hlam, p2647_0]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h2541, hlam, p2647_0]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h2372, hc01, hc15, hlam, hphi, p2647_1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h2538, hlam, p2647_1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h2540, hlam, p2647_0]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [h1479, h2540, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2647_1, u3elo1]
                                · have p2647_0 := h2647c.1
                                  have p2647_1 := h2647c.2.1
                                  have p2647_2 := h2647c.2.2.1
                                  have p2647_3 := h2647c.2.2.2
                                  linarith only [hlam, p2647_0]
                          · linarith only [h1479, h2540, h2642, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1479, h2539, h2641, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1479, h2638, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2538, h2540, h2637, hc01, hlam, hphi, ht12, ht23, u3elo0]
                · linarith only [h0, h2636, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2678 | h2678
              · linarith only [h2539, h2540, h2678, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2680 | h2680
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2681 | h2681
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2682 | h2682
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2683 | h2683
                      · linarith only [h2008, h2678, h2682, h2683, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2685 | h2685
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2686 | h2686
                          · linarith only [h2540, h2686, hc03, hlam, hphi, u3elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2688 | h2688
                            · linarith only [h2008, h2683, h2688, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2690 | h2690
                              · linarith only [h2008, h2536, h2540, h2683, h2685, h2690, hc01, hlam, hphi, ht12, ht23, u3elo4]
                              · rcases h0bigk with h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [hlam, p2692_0]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h0, hlam, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h1479, hlam, p2692_0]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2008, hlam, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2372, hlam, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [hlam, p2692_0]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h0, h2536, h2685, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h0, h2008, hc01, hc12, hlam, hphi, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h0, h2536, h2540, h2685, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2540, hc01, hlam, hphi, ht12, ht23, p2692_1, u3elo4]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2536, hlam, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [hlam, p2692_0]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2008, h2540, hc01, hlam, hphi, ht12, ht23, p2692_1, u3elo4]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2540, hlam, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2008, hc01, hc14, hlam, hphi, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2537, hlam, p2692_0]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2539, hlam, p2692_0]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [hlam, p2692_0]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2678, hlam, p2692_0]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2372, hc01, hc15, hlam, hphi, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2538, hlam, p2692_1]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2540, hc03, hlam, hphi, p2692_1, u3elo4]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [h2008, h2540, hc01, hlam, hphi, ht12, ht23, p2692_1, u3elo4]
                                · have p2692_0 := h2692c.1
                                  have p2692_1 := h2692c.2.1
                                  have p2692_2 := h2692c.2.2.1
                                  have p2692_3 := h2692c.2.2.2
                                  linarith only [hlam, p2692_0]
                        · linarith only [h2539, h2685, hc23, hlam, hphi, u3elo0]
                    · linarith only [h2539, h2540, h2682, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h2538, h2540, h2681, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h0, h2680, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2722 | h2722
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2723 | h2723
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2724 | h2724
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2725 | h2725
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2726 | h2726
                    · linarith only [h2539, h2722, h2726, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h1479, h2726, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2538, h2725, hlam]
                · linarith only [h0, h2536, h2724, hlam]
              · linarith only [h2539, h2722, h2723, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2732 | h2732
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2733 | h2733
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2734 | h2734
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2735 | h2735
                    · linarith only [h2539, h2735, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1479, h2735, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2538, h2734, hlam]
                · linarith only [h0, h2536, h2733, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2740 | h2740
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2741 | h2741
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2742 | h2742
                    · linarith only [h1479, h2539, h2742, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1479, h2742, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2538, h2741, hlam]
                · linarith only [h0, h2536, h2740, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2747 | h2747
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2748 | h2748
            · linarith only [h2536, h2538, h2748, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2750 | h2750
              · linarith only [h2537, h2538, h2750, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2752 | h2752
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2753 | h2753
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2754 | h2754
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2755 | h2755
                      · linarith only [h2008, h2750, h2754, h2755, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2757 | h2757
                        · linarith only [h2536, h2538, h2753, h2757, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h2747, h2748, h2757, hc23, hlam, hphi, u3elo4]
                    · linarith only [h2747, h2748, h2754, hc13, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2761 | h2761
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2762 | h2762
                      · linarith only [h2008, h2750, h2761, h2762, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2764 | h2764
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2765 | h2765
                          · linarith only [h2748, h2765, hc03, hlam, hphi, u3elo2]
                          · linarith only [h0, h2753, h2765, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h2747, h2764, hc23, hlam, hphi, u3elo0]
                    · linarith only [h2747, h2748, h2761, hc13, hlam, hphi, u3elo4]
                · linarith only [h0, h2752, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2771 | h2771
            · linarith only [h2537, h2538, h2747, h2771, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2773 | h2773
              · linarith only [h2537, h2538, h2773, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2775 | h2775
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2776 | h2776
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2777 | h2777
                    · linarith only [h2747, h2777, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1479, h2777, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2780 | h2780
                    · linarith only [h2747, h2780, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1479, h2780, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h2775, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2784 | h2784
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2785 | h2785
          · linarith only [h2536, h2537, h2785, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2787 | h2787
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2788 | h2788
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2789 | h2789
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2790 | h2790
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2791 | h2791
                    · linarith only [h2785, h2787, h2791, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h1479, h2791, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2784, h2787, h2790, hc01, hlam, hphi, ht12, ht23, u3elo0]
                · linarith only [h0, h2536, h2789, hlam]
              · linarith only [h2536, h2537, h2785, h2787, h2788, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2797 | h2797
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2798 | h2798
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2799 | h2799
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2800 | h2800
                    · linarith only [h2785, h2800, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1479, h2800, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1479, h2008, h2537, h2784, h2798, h2799, hc01, hc14, hlam, hphi]
                · linarith only [h0, h2798, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h2537, h2784, h2797, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2806 | h2806
          · linarith only [h2536, h2537, h2806, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2808 | h2808
            · linarith only [h2536, h2784, h2806, h2808, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2810 | h2810
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2811 | h2811
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2812 | h2812
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2813 | h2813
                    · linarith only [h1479, h2806, h2813, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1479, h2813, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2816 | h2816
                    · linarith only [h1479, h2806, h2816, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1479, h2816, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h2811, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2820 | h2820
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2821 | h2821
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2822 | h2822
                    · linarith only [h1479, h2806, h2822, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1479, h2822, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2825 | h2825
                    · linarith only [h1479, h2806, h2825, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1479, h2825, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h2536, h2820, hc01, hlam, hphi, ht12, ht23, u3elo0]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2829 | h2829
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2830 | h2830
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2831 | h2831
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2832 | h2832
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2833 | h2833
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2834 | h2834
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2835 | h2835
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2836 | h2836
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2837 | h2837
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2838 | h2838
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2839 | h2839
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2840 | h2840
                            · linarith only [h2536, h2829, h2834, h2840, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h2536, h2829, h2833, h2834, h2838, h2840, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h2536, h2839, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h2536, h2838, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h2536, h2829, h2833, h2834, h2837, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2536, h2829, h2831, h2834, h2836, hlam]
                  · linarith only [h2536, h2830, h2834, h2835, hlam]
                · linarith only [h0, h2834, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2849 | h2849
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2850 | h2850
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2851 | h2851
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2852 | h2852
                      · linarith only [h2008, h2833, h2851, h2852, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2854 | h2854
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2855 | h2855
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2856 | h2856
                            · linarith only [h2008, h2829, h2852, h2856, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2858 | h2858
                              · linarith only [h2008, h2536, h2830, h2849, h2852, h2854, h2856, h2858, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases h0bigk with h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [hlam, p2860_0]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h0, hlam, p2860_1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h1479, hlam, p2860_0]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2008, hlam, p2860_1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2372, hlam, p2860_1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2536, h2849, hc01, hlam, hphi, ht12, ht23, p2860_1, u3elo1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [hlam, p2860_0]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2536, hlam, p2860_0]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2008, h2536, h2849, hc01, hlam, hphi, ht12, ht23, p2860_1, u3elo1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2536, h2849, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2860_1, u3elo1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2536, h2849, hc01, hlam, hphi, ht12, ht23, p2860_1, u3elo1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2536, h2849, hc02, hlam, hphi, ht23, p2860_1, u3elo1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [hlam, p2860_0]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2008, h2536, h2849, hc01, hlam, hphi, ht12, ht23, p2860_1, u3elo1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2372, h2536, h2849, hc01, hlam, hphi, ht12, ht23, p2860_1, u3elo1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2008, hc01, hc14, hlam, hphi, p2860_1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2829, hlam, p2860_0]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2831, hlam, p2860_0]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [hlam, p2860_0]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2833, hlam, p2860_0]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2372, hc01, hc15, hlam, hphi, p2860_1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2830, hlam, p2860_1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h2832, hlam, p2860_0]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [h0, h2008, h2830, hc01, hc12, hlam, hphi, p2860_1]
                                · have p2860_0 := h2860c.1
                                  have p2860_1 := h2860c.2.1
                                  have p2860_2 := h2860c.2.2.1
                                  have p2860_3 := h2860c.2.2.2
                                  linarith only [hlam, p2860_0]
                          · linarith only [h2536, h2855, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h2536, h2854, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h1479, h2851, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2536, h2830, h2849, h2850, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h0, h2849, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2536, h2830, h2832, hlam]
          · linarith only [h2536, h2829, h2831, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2893 | h2893
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2894 | h2894
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2895 | h2895
              · linarith only [h2829, h2830, h2895, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2897 | h2897
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2898 | h2898
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2899 | h2899
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2900 | h2900
                      · linarith only [h2008, h2895, h2899, h2900, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2902 | h2902
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2903 | h2903
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2904 | h2904
                            · linarith only [h2829, h2830, h2898, h2900, h2904, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2906 | h2906
                              · linarith only [h2829, h2830, h2897, h2900, h2902, h2903, h2906, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · rcases h0bigk with h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c | h2908c
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [hlam, p2908_0]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h0, hlam, p2908_1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h1479, hlam, p2908_0]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2008, hlam, p2908_1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2372, hlam, p2908_1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2830, h2897, h2903, hc01, hlam, hphi, ht12, ht23, p2908_1, u3elo1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [hlam, p2908_0]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2536, hlam, p2908_0]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2008, h2830, h2897, h2903, hc01, hlam, hphi, ht12, ht23, p2908_1, u3elo1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2830, hlam, p2908_0]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2536, h2897, hc01, hlam, hphi, ht12, ht23, p2908_1, u3elo1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2536, h2829, h2897, h2902, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2908_1, u3elo1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [hlam, p2908_0]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2008, h2536, h2897, hc01, hlam, hphi, ht12, ht23, p2908_1, u3elo1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2536, h2829, h2830, h2897, h2902, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2908_1, u3elo1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2008, hc01, hc14, hlam, hphi, p2908_1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2829, hlam, p2908_0]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2893, hlam, p2908_0]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [hlam, p2908_0]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2895, hlam, p2908_0]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2372, hc01, hc15, hlam, hphi, p2908_1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2829, h2830, h2897, h2902, h2903, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2908_1, u3elo1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2894, hlam, p2908_0]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [h2830, h2897, h2903, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2908_1, u3elo1]
                                · have p2908_0 := h2908c.1
                                  have p2908_1 := h2908c.2.1
                                  have p2908_2 := h2908c.2.2.1
                                  have p2908_3 := h2908c.2.2.2
                                  linarith only [hlam, p2908_0]
                          · linarith only [h2536, h2894, h2903, hlam]
                        · linarith only [h2536, h2902, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h2893, h2899, hc13, hlam, hphi, u3elo0]
                  · linarith only [h2536, h2829, h2897, h2898, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h2897, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2939 | h2939
              · linarith only [h2829, h2830, h2939, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2941 | h2941
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2942 | h2942
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2943 | h2943
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2944 | h2944
                      · linarith only [h2008, h2939, h2943, h2944, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2946 | h2946
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2947 | h2947
                          · linarith only [h2894, h2941, h2947, hc03, hlam, hphi, u3elo1]
                          · linarith only [h2536, h2829, h2946, h2947, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h2536, h2829, h2946, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h2893, h2894, h2943, hc13, hlam, hphi, u3elo4]
                  · linarith only [h2536, h2829, h2941, h2942, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h2941, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h2536, h2829, h2893, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2955 | h2955
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2956 | h2956
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2957 | h2957
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2958 | h2958
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2959 | h2959
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2960 | h2960
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2961 | h2961
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2962 | h2962
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2963 | h2963
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2964 | h2964
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2965 | h2965
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2966 | h2966
                              · rcases h0bigk with h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c | h2967c
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [hlam, p2967_0]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h0, hlam, p2967_1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h1479, hlam, p2967_0]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2008, hlam, p2967_1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2372, hlam, p2967_1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2829, h2959, h2963, hc01, hlam, hphi, ht12, ht23, p2967_1, u3elo1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [hlam, p2967_0]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2536, hlam, p2967_0]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2829, hlam, p2967_1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2829, h2959, h2963, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2967_1, u3elo1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p2967_1, u3elo0]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2536, h2959, hc02, hlam, hphi, ht23, p2967_1, u3elo1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [hlam, p2967_0]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2536, h2829, h2955, h2959, h2964, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2967_1, u3elo1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2372, h2536, h2959, hc01, hlam, hphi, ht12, ht23, p2967_1, u3elo1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2008, h2961, hc01, hlam, hphi, ht12, ht23, p2967_1, u3elo1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2829, h2955, h2959, h2963, h2964, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2967_1, u3elo1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2956, hlam, p2967_0]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [hlam, p2967_0]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2372, h2829, h2959, h2963, hc01, hlam, hphi, ht12, ht23, p2967_1, u3elo1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2372, h2961, h2962, hc01, hlam, hphi, ht12, ht23, p2967_1, u3elo1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2955, hlam, p2967_1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2957, hlam, p2967_0]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [h2958, hlam, p2967_1]
                                · have p2967_0 := h2967c.1
                                  have p2967_1 := h2967c.2.1
                                  have p2967_2 := h2967c.2.2.1
                                  have p2967_3 := h2967c.2.2.2
                                  linarith only [hlam, p2967_0]
                              · linarith only [h2829, h2955, h2959, h2963, h2965, h2966, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h2829, h2958, h2965, hlam]
                          · linarith only [h2829, h2963, h2964, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h2536, h2955, h2963, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h2008, h2536, h2955, h2958, h2959, h2962, hc01, hc12, hlam, hphi]
                    · linarith only [h2536, h2956, h2959, h2961, hlam]
                  · linarith only [h2536, h2955, h2959, h2960, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h0, h2959, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h2829, h2955, h2958, hlam]
            · linarith only [h2829, h2955, h2956, h2957, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3003 | h3003
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3004 | h3004
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3005 | h3005
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3006 | h3006
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3007 | h3007
                    · linarith only [h2956, h3007, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1479, h3007, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2536, h2955, h3005, h3006, hlam]
                · linarith only [h0, h3005, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h2536, h2955, h2956, h3004, hlam]
            · linarith only [h2536, h2955, h3003, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3014 | h3014
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3015 | h3015
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3016 | h3016
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3017 | h3017
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3018 | h3018
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3019 | h3019
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3020 | h3020
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3021 | h3021
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3022 | h3022
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3023 | h3023
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3024 | h3024
                              · rcases h0bigk with h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c | h3025c
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [hlam, p3025_0]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h0, hlam, p3025_1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h1479, hlam, p3025_0]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h2008, hlam, p3025_1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h2372, hlam, p3025_1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h2955, h3018, h3020, hc01, hc14, hlam, hphi, p3025_1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [hlam, p3025_0]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h2536, hlam, p3025_0]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h2829, hlam, p3025_1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h2955, hlam, p3025_0]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p3025_1, u3elo0]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h2536, h3017, hc02, hlam, hphi, ht23, p3025_1, u3elo1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [hlam, p3025_0]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h2536, h3017, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3025_1, u3elo1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h0, h2536, h2955, h3017, hc01, hlam, hphi, ht12, ht23, p3025_1, u3elo1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h2008, hc01, hc14, hlam, hphi, p3025_1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h0, h2829, h3017, h3021, hc01, hlam, hphi, ht12, ht23, p3025_1, u3elo1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h3014, hlam, p3025_0]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [hlam, p3025_0]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h0, h2829, h2955, h3017, h3021, hc01, hlam, hphi, ht12, ht23, p3025_1, u3elo1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h2372, h3020, hc01, hc14, hlam, hphi, p3025_1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h0, h2955, h3018, h3020, hc01, hc14, hlam, hphi, p3025_1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h3015, hlam, p3025_0]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [h3016, hlam, p3025_1]
                                · have p3025_0 := h3025c.1
                                  have p3025_1 := h3025c.2.1
                                  have p3025_2 := h3025c.2.2.1
                                  have p3025_3 := h3025c.2.2.2
                                  linarith only [hlam, p3025_0]
                              · rcases h0bigk with h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h0, hlam, p3051_1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h1479, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2008, hlam, p3051_1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2372, hlam, p3051_1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p3051_1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2536, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2829, hlam, p3051_1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2955, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2536, h3017, hc01, hlam, hphi, ht12, ht23, p3051_1, u3elo1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2536, h3017, hc02, hlam, hphi, ht23, p3051_1, u3elo1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2536, h3017, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3051_1, u3elo1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2536, h3017, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3051_1, u3elo1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2008, h3019, hc01, hlam, hphi, ht12, ht23, p3051_1, u3elo1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h0, h2829, h3017, h3021, hc01, hlam, hphi, ht12, ht23, p3051_1, u3elo1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h3014, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h0, h2829, h2955, h3017, h3021, hc01, hlam, hphi, ht12, ht23, p3051_1, u3elo1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2372, h3019, h3020, hc01, hlam, hphi, ht12, ht23, p3051_1, u3elo1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h0, h2955, h3018, h3019, h3020, hc01, hlam, hphi, ht12, ht23, p3051_1, u3elo1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h3015, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h3016, hlam, p3051_1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [hlam, p3051_0]
                            · linarith only [h2829, h3016, h3023, hlam]
                          · linarith only [h0, h2536, h3022, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h2536, h3021, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h2008, h2536, h3014, h3016, h3020, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h2536, h3014, h3017, h3019, hlam]
                  · linarith only [h0, h2536, h3017, h3018, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h3017, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3084 | h3084
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3085 | h3085
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3086 | h3086
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3087 | h3087
                      · linarith only [h2008, h3016, h3086, h3087, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3089 | h3089
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3090 | h3090
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3091 | h3091
                            · linarith only [h2008, h3087, h3091, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3093 | h3093
                              · linarith only [h0, h2829, h3091, h3093, hc01, hlam, hphi, ht12, ht23, u3elo3]
                              · rcases h0bigk with h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c | h3095c
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [hlam, p3095_0]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h0, hlam, p3095_1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h1479, hlam, p3095_0]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h2008, hlam, p3095_1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h2372, hlam, p3095_1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h2829, h3084, h3090, h3091, hc01, hc12, hlam, hphi, p3095_1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [hlam, p3095_0]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h2536, hlam, p3095_0]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h2829, hlam, p3095_1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h2955, hlam, p3095_0]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p3095_1, u3elo0]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h2536, h3084, hc02, hlam, hphi, ht23, p3095_1, u3elo1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [hlam, p3095_0]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h0, h2536, h2829, h3084, hc01, hlam, hphi, ht12, ht23, p3095_1, u3elo1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h0, h2536, h2829, h3016, h3084, hc01, hlam, hphi, ht12, ht23, p3095_1, u3elo1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h2008, hc01, hc14, hlam, hphi, p3095_1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h0, h2829, h3091, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3095_1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h3014, hlam, p3095_0]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [hlam, p3095_0]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h3016, hlam, p3095_0]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h2372, hc01, hc15, hlam, hphi, p3095_1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h0, h2955, h3084, h3090, hc01, hlam, hphi, ht12, ht23, p3095_1, u3elo1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h3015, hlam, p3095_0]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [h2955, h3084, h3090, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3095_1, u3elo1]
                                · have p3095_0 := h3095c.1
                                  have p3095_1 := h3095c.2.1
                                  have p3095_2 := h3095c.2.2.1
                                  have p3095_3 := h3095c.2.2.2
                                  linarith only [hlam, p3095_0]
                          · linarith only [h2536, h3015, h3090, hlam]
                        · linarith only [h0, h2008, h2536, h3014, h3087, h3089, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1479, h3086, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2536, h3084, h3085, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h3084, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3126 | h3126
              · linarith only [h3014, h3015, h3126, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3128 | h3128
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3129 | h3129
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3130 | h3130
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3131 | h3131
                      · linarith only [h2008, h3126, h3130, h3131, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3133 | h3133
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3134 | h3134
                          · linarith only [h3015, h3128, h3134, hc03, hlam, hphi, u3elo1]
                          · linarith only [h0, h2536, h3134, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h2536, h3133, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h3014, h3015, h3130, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h2536, h3128, h3129, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h3128, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3141 | h3141
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3142 | h3142
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3143 | h3143
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3144 | h3144
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3145 | h3145
                    · linarith only [h3014, h3145, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1479, h3145, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2536, h3143, h3144, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h3143, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h3014, h3141, h3142, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3151 | h3151
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3152 | h3152
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3153 | h3153
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3154 | h3154
                    · linarith only [h3014, h3154, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1479, h3154, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2536, h3152, h3153, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h3152, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3159 | h3159
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3160 | h3160
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3161 | h3161
                    · linarith only [h0, h2536, h3014, h3161, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1479, h3161, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2536, h3159, h3160, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h3159, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1479 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2008 | h2008
  · exact r1l7_20_13_14_H_I_L_0_L_I_x1_x1_x0 m hb0 hb3 hb4 h0 h1479 h2008
  · exact r1l7_20_13_14_H_I_L_0_L_I_x1_x1_x1 m hb0 hb3 hb4 h0 h1479 h2008

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1479 | h1479
  · exact r1l7_20_13_14_H_I_L_0_L_I_x1_x0 m hb0 hb3 hb4 h0 h1479
  · exact r1l7_20_13_14_H_I_L_0_L_I_x1_x1 m hb0 hb3 hb4 h0 h1479

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0 m hb0 hb3 hb4 h0
  · exact r1l7_20_13_14_H_I_L_0_L_I_x1 m hb0 hb3 hb4 h0

end R2N4
