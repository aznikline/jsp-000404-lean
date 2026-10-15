import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1923 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1924 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1925 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1926 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1928 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1930 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1932 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  rcases m.htr 1 4 5 (by decide) (by decide) with h2424 | h2424
  · rcases m.htr 2 3 4 (by decide) (by decide) with h2425 | h2425
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2426 | h2426
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
              rcases p2429_3 (m.d 0 1) (by simp) with h2431 | h2431
              · rcases p2429_3 (m.d 0 2) (by simp) with h2432 | h2432
                · linarith only [h0, h2432, hlam]
                · rcases p2429_3 (m.d 0 3) (by simp) with h2434 | h2434
                  · linarith only [h1, h2434, hlam]
                  · linarith only [h2434, h4, hlam]
              · linarith only [h0, h2431, hlam]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1923, h1932, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2429_1, u0elo0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1923, h1932, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2429_1, u0elo0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              rcases p2429_3 (m.d 0 1) (by simp) with h2440 | h2440
              · rcases p2429_3 (m.d 0 2) (by simp) with h2441 | h2441
                · linarith only [h0, h2441, hlam]
                · rcases p2429_3 (m.d 0 3) (by simp) with h2443 | h2443
                  · linarith only [h1, h2443, hlam]
                  · linarith only [h1924, h2443, hlam]
              · linarith only [h2440, h3, hlam]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h0, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h4, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1270, hlam, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1799, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1, hlam, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              rcases p2429_3 (m.d 0 1) (by simp) with h2453 | h2453
              · rcases p2429_3 (m.d 0 2) (by simp) with h2454 | h2454
                · linarith only [h2454, h4, hlam]
                · rcases p2429_3 (m.d 0 3) (by simp) with h2456 | h2456
                  · rcases p2429_3 (m.d 0 4) (by simp) with h2457 | h2457
                    · linarith only [h1923, h2457, hlam]
                    · linarith only [h1270, h2457, hlam]
                  · linarith only [h2456, h4, hlam]
              · linarith only [h0, h2453, hlam]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1923, h1926, h1932, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2429_1, u0elo2]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              rcases p2429_3 (m.d 0 1) (by simp) with h2464 | h2464
              · rcases p2429_3 (m.d 0 2) (by simp) with h2465 | h2465
                · linarith only [h2465, h4, hlam]
                · rcases p2429_3 (m.d 0 3) (by simp) with h2467 | h2467
                  · rcases p2429_3 (m.d 0 4) (by simp) with h2468 | h2468
                    · linarith only [h1923, h2468, hlam]
                    · linarith only [h1925, h2468, hlam]
                  · linarith only [h1924, h2467, hlam]
              · linarith only [h2464, h3, hlam]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h2, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              rcases p2429_3 (m.d 0 1) (by simp) with h2474 | h2474
              · rcases p2429_3 (m.d 0 2) (by simp) with h2475 | h2475
                · linarith only [h1270, h2475, hlam]
                · rcases p2429_3 (m.d 0 3) (by simp) with h2477 | h2477
                  · rcases p2429_3 (m.d 0 4) (by simp) with h2478 | h2478
                    · rcases p2429_3 (m.d 0 5) (by simp) with h2479 | h2479
                      · linarith only [h1925, h2479, hlam]
                      · linarith only [h1799, h2479, hlam]
                    · linarith only [h1270, h2478, hlam]
                  · linarith only [h2477, h4, hlam]
              · linarith only [h0, h2474, hlam]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1923, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              rcases p2429_3 (m.d 0 1) (by simp) with h2487 | h2487
              · rcases p2429_3 (m.d 0 2) (by simp) with h2488 | h2488
                · linarith only [h1270, h2488, hlam]
                · rcases p2429_3 (m.d 0 3) (by simp) with h2490 | h2490
                  · rcases p2429_3 (m.d 0 4) (by simp) with h2491 | h2491
                    · rcases p2429_3 (m.d 0 5) (by simp) with h2492 | h2492
                      · linarith only [h1925, h2492, hlam]
                      · rcases h0emin with h2494 | h2494 | h2494 | h2494 | h2494
                        · rcases h2bigk with h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c | h2495c
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h1, h1799, h1923, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2429_1, p2495_1, u0elo0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h4, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h1270, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h1799, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h0, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h1926, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h1928, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h1930, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            rcases p2495_3 (m.d 0 2) (by simp) with h2506 | h2506
                            · linarith only [h2506, hlam, p2495_0]
                            · rcases p2495_3 (m.d 1 2) (by simp) with h2508 | h2508
                              · linarith only [h1926, h2508, hlam]
                              · rcases p2495_3 (m.d 2 3) (by simp) with h2510 | h2510
                                · rcases p2495_3 (m.d 2 4) (by simp) with h2511 | h2511
                                  · linarith only [h2425, h2511, hlam]
                                  · linarith only [h1270, h2511, hlam]
                                · linarith only [h2510, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            rcases p2495_3 (m.d 0 2) (by simp) with h2515 | h2515
                            · linarith only [h2515, h4, hlam]
                            · linarith only [h0, h2515, hlam]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h1270, h1799, hc02, hc23, hlam, hphi, p2429_1, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h0, h1799, hc12, hc23, hlam, hphi, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            rcases p2495_3 (m.d 0 2) (by simp) with h2521 | h2521
                            · linarith only [h2521, hlam, p2495_0]
                            · rcases p2495_3 (m.d 1 2) (by simp) with h2523 | h2523
                              · linarith only [h1928, h2523, hlam]
                              · rcases p2495_3 (m.d 2 3) (by simp) with h2525 | h2525
                                · rcases p2495_3 (m.d 2 4) (by simp) with h2526 | h2526
                                  · rcases p2495_3 (m.d 2 5) (by simp) with h2527 | h2527
                                    · linarith only [h2427, h2527, hlam]
                                    · linarith only [h1799, h2527, hlam]
                                  · linarith only [h2526, hlam, p2495_0]
                                · linarith only [h2525, h4, hlam]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            rcases p2495_3 (m.d 0 2) (by simp) with h2532 | h2532
                            · linarith only [h1270, h2532, hlam]
                            · linarith only [h0, h2532, hlam]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2425, hlam, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h0, h1799, hc12, hc24, hlam, hphi, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            rcases p2495_3 (m.d 0 2) (by simp) with h2538 | h2538
                            · linarith only [h2538, hlam, p2495_0]
                            · rcases p2495_3 (m.d 1 2) (by simp) with h2540 | h2540
                              · linarith only [h1930, h2540, hlam]
                              · rcases p2495_3 (m.d 2 3) (by simp) with h2542 | h2542
                                · rcases p2495_3 (m.d 2 4) (by simp) with h2543 | h2543
                                  · rcases p2495_3 (m.d 2 5) (by simp) with h2544 | h2544
                                    · rcases h4bigk with h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h1, h1923, h2424, hc45, hlam, hphi, ht0b, ht5b, p2545_1, u0elo0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h1270, hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h1, h1923, h1926, h1932, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2545_1, u0elo0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        rcases p2545_3 (m.d 0 4) (by simp) with h2550 | h2550
                                        · rcases p2545_3 (m.d 1 4) (by simp) with h2551 | h2551
                                          · linarith only [h2, h2551, hlam]
                                          · linarith only [h2424, h2551, hlam]
                                        · linarith only [h2550, hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h2, hlam, p2545_1]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h1928, hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h1932, hlam, p2545_1]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p2545_1, u0elo0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h1799, h2425, hc02, hc23, hlam, hphi, p2429_1, p2545_1]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        rcases p2545_3 (m.d 0 4) (by simp) with h2561 | h2561
                                        · linarith only [h1270, h2561, hlam]
                                        · linarith only [h2, h2561, hlam]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h1926, h1932, h2425, hc12, hc23, hlam, hphi, p2545_1]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        rcases p2545_3 (m.d 0 4) (by simp) with h2566 | h2566
                                        · linarith only [h1270, h2566, hlam]
                                        · linarith only [h1925, h2566, hlam]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h1923, hlam, p2545_1]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h1, h1923, hc14, hlam, hphi, ht0b, ht45, ht5b, p2545_1, u0elo0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h2425, hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h1, h1923, hc45, hlam, hphi, ht0b, ht5b, p2545_1, u0elo0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h1925, hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h2424, hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h2427, hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [h2428, hlam, p2545_0]
                                      · have p2545_0 := h2545c.1
                                        have p2545_1 := h2545c.2.1
                                        have p2545_2 := h2545c.2.2.1
                                        have p2545_3 := h2545c.2.2.2
                                        linarith only [hlam, p2545_0]
                                    · linarith only [h2544, hlam, p2495_0]
                                  · linarith only [h1270, h2543, hlam]
                                · linarith only [h2542, h4, hlam]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            rcases p2495_3 (m.d 0 2) (by simp) with h2582 | h2582
                            · linarith only [h1799, h2582, hlam]
                            · linarith only [h0, h2582, hlam]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2426, hlam, p2495_1]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [h2427, hlam, p2495_0]
                          · have p2495_0 := h2495c.1
                            have p2495_1 := h2495c.2.1
                            have p2495_2 := h2495c.2.2.1
                            have p2495_3 := h2495c.2.2.2
                            linarith only [hlam, p2495_0]
                        · linarith only [h1799, h2494, hlam, p2429_1, u0elo3]
                        · rcases h2bigk with h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c | h2589c
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h1, h1799, h1923, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2429_1, p2589_1, u0elo0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h4, hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h1270, hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h1799, hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h0, hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h1926, hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h1928, hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h1930, hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            rcases p2589_3 (m.d 0 2) (by simp) with h2600 | h2600
                            · linarith only [h2600, hlam, p2589_0]
                            · rcases p2589_3 (m.d 1 2) (by simp) with h2602 | h2602
                              · linarith only [h1926, h2602, hlam]
                              · rcases p2589_3 (m.d 2 3) (by simp) with h2604 | h2604
                                · rcases p2589_3 (m.d 2 4) (by simp) with h2605 | h2605
                                  · linarith only [h2425, h2605, hlam]
                                  · linarith only [h1270, h2605, hlam]
                                · linarith only [h2604, hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            rcases p2589_3 (m.d 0 2) (by simp) with h2609 | h2609
                            · linarith only [h2609, h4, hlam]
                            · linarith only [h0, h2609, hlam]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h1270, hc02, hc23, hlam, hphi, p2589_1]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h0, h1799, hc12, hc23, hlam, hphi, p2589_1]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            rcases p2589_3 (m.d 0 2) (by simp) with h2615 | h2615
                            · linarith only [h2615, hlam, p2589_0]
                            · rcases p2589_3 (m.d 1 2) (by simp) with h2617 | h2617
                              · linarith only [h1928, h2617, hlam]
                              · rcases p2589_3 (m.d 2 3) (by simp) with h2619 | h2619
                                · rcases p2589_3 (m.d 2 4) (by simp) with h2620 | h2620
                                  · rcases p2589_3 (m.d 2 5) (by simp) with h2621 | h2621
                                    · linarith only [h2427, h2621, hlam]
                                    · linarith only [h1799, h2621, hlam]
                                  · linarith only [h2620, hlam, p2589_0]
                                · linarith only [h2619, h4, hlam]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            rcases p2589_3 (m.d 0 2) (by simp) with h2626 | h2626
                            · linarith only [h1270, h2626, hlam]
                            · linarith only [h0, h2626, hlam]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h2425, hlam, p2589_1]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h0, h1799, hc12, hc24, hlam, hphi, p2589_1]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            rcases p2589_3 (m.d 0 2) (by simp) with h2632 | h2632
                            · linarith only [h2632, hlam, p2589_0]
                            · rcases p2589_3 (m.d 1 2) (by simp) with h2634 | h2634
                              · linarith only [h1930, h2634, hlam]
                              · rcases p2589_3 (m.d 2 3) (by simp) with h2636 | h2636
                                · rcases p2589_3 (m.d 2 4) (by simp) with h2637 | h2637
                                  · rcases p2589_3 (m.d 2 5) (by simp) with h2638 | h2638
                                    · rcases h4bigk with h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c | h2639c
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h1, h1923, h2424, hc45, hlam, hphi, ht0b, ht5b, p2639_1, u0elo0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h1270, hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h1, h1923, h1926, h1932, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2639_1, u0elo0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        rcases p2639_3 (m.d 0 4) (by simp) with h2644 | h2644
                                        · rcases p2639_3 (m.d 1 4) (by simp) with h2645 | h2645
                                          · linarith only [h2, h2645, hlam]
                                          · linarith only [h2424, h2645, hlam]
                                        · linarith only [h2644, hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h2, hlam, p2639_1]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h1928, hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h1932, hlam, p2639_1]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p2639_1, u0elo0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h2425, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2429_1, p2639_1]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        rcases p2639_3 (m.d 0 4) (by simp) with h2655 | h2655
                                        · linarith only [h1270, h2655, hlam]
                                        · linarith only [h2, h2655, hlam]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h1926, h1932, h2425, hc12, hc23, hlam, hphi, p2639_1]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        rcases p2639_3 (m.d 0 4) (by simp) with h2660 | h2660
                                        · linarith only [h1270, h2660, hlam]
                                        · linarith only [h1925, h2660, hlam]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h1923, hlam, p2639_1]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h1, h1923, hc14, hlam, hphi, ht0b, ht45, ht5b, p2639_1, u0elo0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h2425, hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h1, h1923, hc45, hlam, hphi, ht0b, ht5b, p2639_1, u0elo0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h1925, hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h2424, hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h2427, hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [h2428, hlam, p2639_0]
                                      · have p2639_0 := h2639c.1
                                        have p2639_1 := h2639c.2.1
                                        have p2639_2 := h2639c.2.2.1
                                        have p2639_3 := h2639c.2.2.2
                                        linarith only [hlam, p2639_0]
                                    · linarith only [h2638, hlam, p2589_0]
                                  · linarith only [h1270, h2637, hlam]
                                · linarith only [h2636, h4, hlam]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            rcases p2589_3 (m.d 0 2) (by simp) with h2676 | h2676
                            · linarith only [h1799, h2676, hlam]
                            · linarith only [h0, h2676, hlam]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h2426, hlam, p2589_1]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [h2427, hlam, p2589_0]
                          · have p2589_0 := h2589c.1
                            have p2589_1 := h2589c.2.1
                            have p2589_2 := h2589c.2.2.1
                            have p2589_3 := h2589c.2.2.2
                            linarith only [hlam, p2589_0]
                        · rcases h2bigk with h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h4, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1270, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1799, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h0, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1926, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1928, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1930, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            rcases p2682_3 (m.d 0 2) (by simp) with h2693 | h2693
                            · linarith only [h2693, hlam, p2682_0]
                            · rcases p2682_3 (m.d 1 2) (by simp) with h2695 | h2695
                              · linarith only [h1926, h2695, hlam]
                              · rcases p2682_3 (m.d 2 3) (by simp) with h2697 | h2697
                                · rcases p2682_3 (m.d 2 4) (by simp) with h2698 | h2698
                                  · linarith only [h2425, h2698, hlam]
                                  · linarith only [h1270, h2698, hlam]
                                · linarith only [h2697, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            rcases p2682_3 (m.d 0 2) (by simp) with h2702 | h2702
                            · linarith only [h2702, h4, hlam]
                            · linarith only [h0, h2702, hlam]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1270, hc02, hc23, hlam, hphi, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h0, h1799, hc12, hc23, hlam, hphi, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            rcases p2682_3 (m.d 0 2) (by simp) with h2708 | h2708
                            · linarith only [h2708, hlam, p2682_0]
                            · rcases p2682_3 (m.d 1 2) (by simp) with h2710 | h2710
                              · linarith only [h1928, h2710, hlam]
                              · rcases p2682_3 (m.d 2 3) (by simp) with h2712 | h2712
                                · rcases p2682_3 (m.d 2 4) (by simp) with h2713 | h2713
                                  · rcases p2682_3 (m.d 2 5) (by simp) with h2714 | h2714
                                    · linarith only [h2427, h2714, hlam]
                                    · linarith only [h1799, h2714, hlam]
                                  · linarith only [h2713, hlam, p2682_0]
                                · linarith only [h2712, h4, hlam]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            rcases p2682_3 (m.d 0 2) (by simp) with h2719 | h2719
                            · linarith only [h1270, h2719, hlam]
                            · linarith only [h0, h2719, hlam]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h2425, hlam, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h0, h1799, hc12, hc24, hlam, hphi, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            rcases p2682_3 (m.d 0 2) (by simp) with h2725 | h2725
                            · linarith only [h2725, hlam, p2682_0]
                            · rcases p2682_3 (m.d 1 2) (by simp) with h2727 | h2727
                              · linarith only [h1930, h2727, hlam]
                              · rcases p2682_3 (m.d 2 3) (by simp) with h2729 | h2729
                                · rcases p2682_3 (m.d 2 4) (by simp) with h2730 | h2730
                                  · rcases p2682_3 (m.d 2 5) (by simp) with h2731 | h2731
                                    · rcases h4bigk with h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c | h2732c
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h2424, hc45, hlam, hphi, ht0b, ht5b, p2732_1, u0elo3]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h1270, hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h1, h1923, h1926, h1932, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2732_1, u0elo0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        rcases p2732_3 (m.d 0 4) (by simp) with h2737 | h2737
                                        · rcases p2732_3 (m.d 1 4) (by simp) with h2738 | h2738
                                          · linarith only [h2, h2738, hlam]
                                          · linarith only [h2424, h2738, hlam]
                                        · linarith only [h2737, hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h2, hlam, p2732_1]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h1928, hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h1932, hlam, p2732_1]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p2732_1, u0elo0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h2425, h2494, hc23, hlam, ht01, ht12, p2732_1]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        rcases p2732_3 (m.d 0 4) (by simp) with h2748 | h2748
                                        · linarith only [h1270, h2748, hlam]
                                        · linarith only [h2, h2748, hlam]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h1926, h1932, h2425, hc12, hc23, hlam, hphi, p2732_1]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        rcases p2732_3 (m.d 0 4) (by simp) with h2753 | h2753
                                        · linarith only [h1270, h2753, hlam]
                                        · linarith only [h1925, h2753, hlam]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h1923, hlam, p2732_1]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h1, h1923, hc14, hlam, hphi, ht0b, ht45, ht5b, p2732_1, u0elo0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h2425, hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h1, h1923, hc45, hlam, hphi, ht0b, ht5b, p2732_1, u0elo0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h1925, hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h2424, hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h2427, hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [h2428, hlam, p2732_0]
                                      · have p2732_0 := h2732c.1
                                        have p2732_1 := h2732c.2.1
                                        have p2732_2 := h2732c.2.2.1
                                        have p2732_3 := h2732c.2.2.2
                                        linarith only [hlam, p2732_0]
                                    · linarith only [h2731, hlam, p2682_0]
                                  · linarith only [h1270, h2730, hlam]
                                · linarith only [h2729, h4, hlam]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            rcases p2682_3 (m.d 0 2) (by simp) with h2769 | h2769
                            · linarith only [h1799, h2769, hlam]
                            · linarith only [h0, h2769, hlam]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h2426, hlam, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h2427, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [hlam, p2682_0]
                        · linarith only [h2494, hlam, p2429_1, u0elo3]
                    · linarith only [h1925, h2491, hlam]
                  · linarith only [h1924, h2490, hlam]
              · linarith only [h2487, h3, hlam]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h3, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              rcases p2429_3 (m.d 0 1) (by simp) with h2780 | h2780
              · rcases p2429_3 (m.d 0 2) (by simp) with h2781 | h2781
                · linarith only [h1799, h2781, hlam]
                · rcases p2429_3 (m.d 0 3) (by simp) with h2783 | h2783
                  · rcases p2429_3 (m.d 0 4) (by simp) with h2784 | h2784
                    · rcases p2429_3 (m.d 0 5) (by simp) with h2785 | h2785
                      · rcases h0emin with h2786 | h2786 | h2786 | h2786 | h2786
                        · rcases h2bigk with h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c | h2787c
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2429_1, p2787_1, u0elo4]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h4, hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h1270, hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h1799, hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h0, hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h1926, hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h1928, hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h1930, hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            rcases p2787_3 (m.d 0 2) (by simp) with h2798 | h2798
                            · linarith only [h2798, hlam, p2787_0]
                            · rcases p2787_3 (m.d 1 2) (by simp) with h2800 | h2800
                              · linarith only [h1926, h2800, hlam]
                              · rcases p2787_3 (m.d 2 3) (by simp) with h2802 | h2802
                                · rcases p2787_3 (m.d 2 4) (by simp) with h2803 | h2803
                                  · linarith only [h2425, h2803, hlam]
                                  · linarith only [h1270, h2803, hlam]
                                · linarith only [h2802, hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            rcases p2787_3 (m.d 0 2) (by simp) with h2807 | h2807
                            · linarith only [h2807, h4, hlam]
                            · linarith only [h0, h2807, hlam]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h1270, hc02, hc23, hlam, hphi, p2787_1]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h0, h1799, hc12, hc23, hlam, hphi, p2787_1]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            rcases p2787_3 (m.d 0 2) (by simp) with h2813 | h2813
                            · linarith only [h2813, hlam, p2787_0]
                            · rcases p2787_3 (m.d 1 2) (by simp) with h2815 | h2815
                              · linarith only [h1928, h2815, hlam]
                              · rcases p2787_3 (m.d 2 3) (by simp) with h2817 | h2817
                                · rcases p2787_3 (m.d 2 4) (by simp) with h2818 | h2818
                                  · rcases p2787_3 (m.d 2 5) (by simp) with h2819 | h2819
                                    · linarith only [h2427, h2819, hlam]
                                    · linarith only [h1799, h2819, hlam]
                                  · linarith only [h2818, hlam, p2787_0]
                                · linarith only [h2817, h4, hlam]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            rcases p2787_3 (m.d 0 2) (by simp) with h2824 | h2824
                            · linarith only [h1270, h2824, hlam]
                            · linarith only [h0, h2824, hlam]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h2425, hlam, p2787_1]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h0, h1799, hc12, hc24, hlam, hphi, p2429_1, p2787_1]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            rcases p2787_3 (m.d 0 2) (by simp) with h2830 | h2830
                            · linarith only [h2830, hlam, p2787_0]
                            · rcases p2787_3 (m.d 1 2) (by simp) with h2832 | h2832
                              · linarith only [h1930, h2832, hlam]
                              · rcases p2787_3 (m.d 2 3) (by simp) with h2834 | h2834
                                · rcases p2787_3 (m.d 2 4) (by simp) with h2835 | h2835
                                  · rcases p2787_3 (m.d 2 5) (by simp) with h2836 | h2836
                                    · rcases h4bigk with h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c | h2837c
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h1, h1923, h2424, hc45, hlam, hphi, ht0b, ht5b, p2837_1, u0elo0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h1270, hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h1, h1923, h1926, h1932, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2837_1, u0elo0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        rcases p2837_3 (m.d 0 4) (by simp) with h2842 | h2842
                                        · rcases p2837_3 (m.d 1 4) (by simp) with h2843 | h2843
                                          · linarith only [h2, h2843, hlam]
                                          · linarith only [h2424, h2843, hlam]
                                        · linarith only [h2842, hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h2, hlam, p2837_1]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h1928, hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h1932, hlam, p2837_1]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p2837_1, u0elo0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h1923, h1926, h1932, h2425, hc12, hc23, hlam, hphi, p2837_1]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        rcases p2837_3 (m.d 0 4) (by simp) with h2853 | h2853
                                        · linarith only [h1270, h2853, hlam]
                                        · linarith only [h2, h2853, hlam]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h1926, h1932, h2425, hc12, hc23, hlam, hphi, p2837_1]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        rcases p2837_3 (m.d 0 4) (by simp) with h2858 | h2858
                                        · linarith only [h1270, h2858, hlam]
                                        · linarith only [h1925, h2858, hlam]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h1923, hlam, p2837_1]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h1, h1923, hc14, hlam, hphi, ht0b, ht45, ht5b, p2837_1, u0elo0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h2425, hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h1, h1923, hc45, hlam, hphi, ht0b, ht5b, p2837_1, u0elo0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h1925, hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h2424, hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h2427, hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [h2428, hlam, p2837_0]
                                      · have p2837_0 := h2837c.1
                                        have p2837_1 := h2837c.2.1
                                        have p2837_2 := h2837c.2.2.1
                                        have p2837_3 := h2837c.2.2.2
                                        linarith only [hlam, p2837_0]
                                    · linarith only [h2836, hlam, p2787_0]
                                  · linarith only [h1270, h2835, hlam]
                                · linarith only [h2834, h4, hlam]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            rcases p2787_3 (m.d 0 2) (by simp) with h2874 | h2874
                            · linarith only [h1799, h2874, hlam]
                            · linarith only [h0, h2874, hlam]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h2426, hlam, p2787_1]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [h2427, hlam, p2787_0]
                          · have p2787_0 := h2787c.1
                            have p2787_1 := h2787c.2.1
                            have p2787_2 := h2787c.2.2.1
                            have p2787_3 := h2787c.2.2.2
                            linarith only [hlam, p2787_0]
                        · linarith only [h1925, h2786, hlam, p2429_1, u0elo3]
                        · rcases h2bigk with h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h1, h1923, h1925, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2429_1, p2881_1, u0elo0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h4, hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h1270, hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h1799, hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h0, hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h1926, hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h1928, hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h1930, hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            rcases p2881_3 (m.d 0 2) (by simp) with h2892 | h2892
                            · linarith only [h2892, hlam, p2881_0]
                            · rcases p2881_3 (m.d 1 2) (by simp) with h2894 | h2894
                              · linarith only [h1926, h2894, hlam]
                              · rcases p2881_3 (m.d 2 3) (by simp) with h2896 | h2896
                                · rcases p2881_3 (m.d 2 4) (by simp) with h2897 | h2897
                                  · linarith only [h2425, h2897, hlam]
                                  · linarith only [h1270, h2897, hlam]
                                · linarith only [h2896, hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            rcases p2881_3 (m.d 0 2) (by simp) with h2901 | h2901
                            · linarith only [h2901, h4, hlam]
                            · linarith only [h0, h2901, hlam]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h1270, hc02, hc23, hlam, hphi, p2881_1]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h0, h1799, hc12, hc23, hlam, hphi, p2881_1]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            rcases p2881_3 (m.d 0 2) (by simp) with h2907 | h2907
                            · linarith only [h2907, hlam, p2881_0]
                            · rcases p2881_3 (m.d 1 2) (by simp) with h2909 | h2909
                              · linarith only [h1928, h2909, hlam]
                              · rcases p2881_3 (m.d 2 3) (by simp) with h2911 | h2911
                                · rcases p2881_3 (m.d 2 4) (by simp) with h2912 | h2912
                                  · rcases p2881_3 (m.d 2 5) (by simp) with h2913 | h2913
                                    · linarith only [h2427, h2913, hlam]
                                    · linarith only [h1799, h2913, hlam]
                                  · linarith only [h2912, hlam, p2881_0]
                                · linarith only [h2911, h4, hlam]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            rcases p2881_3 (m.d 0 2) (by simp) with h2918 | h2918
                            · linarith only [h1270, h2918, hlam]
                            · linarith only [h0, h2918, hlam]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h2425, hlam, p2881_1]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h0, h1799, hc12, hc24, hlam, hphi, p2429_1, p2881_1]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            rcases p2881_3 (m.d 0 2) (by simp) with h2924 | h2924
                            · linarith only [h2924, hlam, p2881_0]
                            · rcases p2881_3 (m.d 1 2) (by simp) with h2926 | h2926
                              · linarith only [h1930, h2926, hlam]
                              · rcases p2881_3 (m.d 2 3) (by simp) with h2928 | h2928
                                · rcases p2881_3 (m.d 2 4) (by simp) with h2929 | h2929
                                  · rcases p2881_3 (m.d 2 5) (by simp) with h2930 | h2930
                                    · rcases h4bigk with h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c | h2931c
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h1, h1923, h2424, hc45, hlam, hphi, ht0b, ht5b, p2931_1, u0elo0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h1270, hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h1, h1923, h1926, h1932, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2931_1, u0elo0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        rcases p2931_3 (m.d 0 4) (by simp) with h2936 | h2936
                                        · rcases p2931_3 (m.d 1 4) (by simp) with h2937 | h2937
                                          · linarith only [h2, h2937, hlam]
                                          · linarith only [h2424, h2937, hlam]
                                        · linarith only [h2936, hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h2, hlam, p2931_1]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h1928, hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h1932, hlam, p2931_1]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p2931_1, u0elo0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h1923, h1926, h1932, h2425, hc12, hc23, hlam, hphi, p2931_1]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        rcases p2931_3 (m.d 0 4) (by simp) with h2947 | h2947
                                        · linarith only [h1270, h2947, hlam]
                                        · linarith only [h2, h2947, hlam]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h1926, h1932, h2425, hc12, hc23, hlam, hphi, p2931_1]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        rcases p2931_3 (m.d 0 4) (by simp) with h2952 | h2952
                                        · linarith only [h1270, h2952, hlam]
                                        · linarith only [h1925, h2952, hlam]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h1923, hlam, p2931_1]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h1, h1923, hc14, hlam, hphi, ht0b, ht45, ht5b, p2931_1, u0elo0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h2425, hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h1, h1923, hc45, hlam, hphi, ht0b, ht5b, p2931_1, u0elo0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h1925, hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h2424, hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h2427, hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [h2428, hlam, p2931_0]
                                      · have p2931_0 := h2931c.1
                                        have p2931_1 := h2931c.2.1
                                        have p2931_2 := h2931c.2.2.1
                                        have p2931_3 := h2931c.2.2.2
                                        linarith only [hlam, p2931_0]
                                    · linarith only [h2930, hlam, p2881_0]
                                  · linarith only [h1270, h2929, hlam]
                                · linarith only [h2928, h4, hlam]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            rcases p2881_3 (m.d 0 2) (by simp) with h2968 | h2968
                            · linarith only [h1799, h2968, hlam]
                            · linarith only [h0, h2968, hlam]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h2426, hlam, p2881_1]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [h2427, hlam, p2881_0]
                          · have p2881_0 := h2881c.1
                            have p2881_1 := h2881c.2.1
                            have p2881_2 := h2881c.2.2.1
                            have p2881_3 := h2881c.2.2.2
                            linarith only [hlam, p2881_0]
                        · rcases h2bigk with h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c | h2974c
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h1925, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2429_1, p2974_1, u0elo3]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h4, hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h1270, hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h1799, hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h0, hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h1926, hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h1928, hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h1930, hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            rcases p2974_3 (m.d 0 2) (by simp) with h2985 | h2985
                            · linarith only [h2985, hlam, p2974_0]
                            · rcases p2974_3 (m.d 1 2) (by simp) with h2987 | h2987
                              · linarith only [h1926, h2987, hlam]
                              · rcases p2974_3 (m.d 2 3) (by simp) with h2989 | h2989
                                · rcases p2974_3 (m.d 2 4) (by simp) with h2990 | h2990
                                  · linarith only [h2425, h2990, hlam]
                                  · linarith only [h1270, h2990, hlam]
                                · linarith only [h2989, hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            rcases p2974_3 (m.d 0 2) (by simp) with h2994 | h2994
                            · linarith only [h2994, h4, hlam]
                            · linarith only [h0, h2994, hlam]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h1270, hc02, hc23, hlam, hphi, p2974_1]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h0, h1799, hc12, hc23, hlam, hphi, p2974_1]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            rcases p2974_3 (m.d 0 2) (by simp) with h3000 | h3000
                            · linarith only [h3000, hlam, p2974_0]
                            · rcases p2974_3 (m.d 1 2) (by simp) with h3002 | h3002
                              · linarith only [h1928, h3002, hlam]
                              · rcases p2974_3 (m.d 2 3) (by simp) with h3004 | h3004
                                · rcases p2974_3 (m.d 2 4) (by simp) with h3005 | h3005
                                  · rcases p2974_3 (m.d 2 5) (by simp) with h3006 | h3006
                                    · linarith only [h2427, h3006, hlam]
                                    · linarith only [h1799, h3006, hlam]
                                  · linarith only [h3005, hlam, p2974_0]
                                · linarith only [h3004, h4, hlam]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            rcases p2974_3 (m.d 0 2) (by simp) with h3011 | h3011
                            · linarith only [h1270, h3011, hlam]
                            · linarith only [h0, h3011, hlam]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h2425, hlam, p2974_1]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h0, h1799, hc12, hc24, hlam, hphi, p2429_1, p2974_1]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            rcases p2974_3 (m.d 0 2) (by simp) with h3017 | h3017
                            · linarith only [h3017, hlam, p2974_0]
                            · rcases p2974_3 (m.d 1 2) (by simp) with h3019 | h3019
                              · linarith only [h1930, h3019, hlam]
                              · rcases p2974_3 (m.d 2 3) (by simp) with h3021 | h3021
                                · rcases p2974_3 (m.d 2 4) (by simp) with h3022 | h3022
                                  · rcases p2974_3 (m.d 2 5) (by simp) with h3023 | h3023
                                    · rcases h4bigk with h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c | h3024c
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h1, h1923, h2424, hc45, hlam, hphi, ht0b, ht5b, p3024_1, u0elo0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h1270, hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h1, h1923, h1926, h1932, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3024_1, u0elo0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        rcases p3024_3 (m.d 0 4) (by simp) with h3029 | h3029
                                        · rcases p3024_3 (m.d 1 4) (by simp) with h3030 | h3030
                                          · linarith only [h2, h3030, hlam]
                                          · linarith only [h2424, h3030, hlam]
                                        · linarith only [h3029, hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h2, hlam, p3024_1]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h1928, hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h1932, hlam, p3024_1]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p3024_1, u0elo0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h2425, h2786, hc23, hlam, ht01, ht12, p3024_1]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        rcases p3024_3 (m.d 0 4) (by simp) with h3040 | h3040
                                        · linarith only [h1270, h3040, hlam]
                                        · linarith only [h2, h3040, hlam]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h1926, h1932, h2425, hc12, hc23, hlam, hphi, p3024_1]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        rcases p3024_3 (m.d 0 4) (by simp) with h3045 | h3045
                                        · linarith only [h1270, h3045, hlam]
                                        · linarith only [h1925, h3045, hlam]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h1923, hlam, p3024_1]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h1, h1923, hc14, hlam, hphi, ht0b, ht45, ht5b, p3024_1, u0elo0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h2425, hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h1, h1923, hc45, hlam, hphi, ht0b, ht5b, p3024_1, u0elo0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h1925, hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h2424, hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h2427, hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [h2428, hlam, p3024_0]
                                      · have p3024_0 := h3024c.1
                                        have p3024_1 := h3024c.2.1
                                        have p3024_2 := h3024c.2.2.1
                                        have p3024_3 := h3024c.2.2.2
                                        linarith only [hlam, p3024_0]
                                    · linarith only [h3023, hlam, p2974_0]
                                  · linarith only [h1270, h3022, hlam]
                                · linarith only [h3021, h4, hlam]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            rcases p2974_3 (m.d 0 2) (by simp) with h3061 | h3061
                            · linarith only [h1799, h3061, hlam]
                            · linarith only [h0, h3061, hlam]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h2426, hlam, p2974_1]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [h2427, hlam, p2974_0]
                          · have p2974_0 := h2974c.1
                            have p2974_1 := h2974c.2.1
                            have p2974_2 := h2974c.2.2.1
                            have p2974_3 := h2974c.2.2.2
                            linarith only [hlam, p2974_0]
                        · rcases h2bigk with h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h1925, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2429_1, p3067_1, u0elo3]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h4, hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h1270, hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h1799, hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h0, hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h1926, hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h1928, hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h1930, hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            rcases p3067_3 (m.d 0 2) (by simp) with h3078 | h3078
                            · linarith only [h3078, hlam, p3067_0]
                            · rcases p3067_3 (m.d 1 2) (by simp) with h3080 | h3080
                              · linarith only [h1926, h3080, hlam]
                              · rcases p3067_3 (m.d 2 3) (by simp) with h3082 | h3082
                                · rcases p3067_3 (m.d 2 4) (by simp) with h3083 | h3083
                                  · linarith only [h2425, h3083, hlam]
                                  · linarith only [h1270, h3083, hlam]
                                · linarith only [h3082, hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            rcases p3067_3 (m.d 0 2) (by simp) with h3087 | h3087
                            · linarith only [h3087, h4, hlam]
                            · linarith only [h0, h3087, hlam]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h1270, hc02, hc23, hlam, hphi, p3067_1]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h1799, h2786, hc23, hlam, ht01, ht12, p3067_1]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            rcases p3067_3 (m.d 0 2) (by simp) with h3093 | h3093
                            · linarith only [h3093, hlam, p3067_0]
                            · rcases p3067_3 (m.d 1 2) (by simp) with h3095 | h3095
                              · linarith only [h1928, h3095, hlam]
                              · rcases p3067_3 (m.d 2 3) (by simp) with h3097 | h3097
                                · rcases p3067_3 (m.d 2 4) (by simp) with h3098 | h3098
                                  · rcases p3067_3 (m.d 2 5) (by simp) with h3099 | h3099
                                    · linarith only [h2427, h3099, hlam]
                                    · linarith only [h1799, h3099, hlam]
                                  · linarith only [h3098, hlam, p3067_0]
                                · linarith only [h3097, h4, hlam]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            rcases p3067_3 (m.d 0 2) (by simp) with h3104 | h3104
                            · linarith only [h1270, h3104, hlam]
                            · linarith only [h0, h3104, hlam]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h2425, hlam, p3067_1]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h0, h1799, hc12, hc24, hlam, hphi, p2429_1, p3067_1]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            rcases p3067_3 (m.d 0 2) (by simp) with h3110 | h3110
                            · linarith only [h3110, hlam, p3067_0]
                            · rcases p3067_3 (m.d 1 2) (by simp) with h3112 | h3112
                              · linarith only [h1930, h3112, hlam]
                              · rcases p3067_3 (m.d 2 3) (by simp) with h3114 | h3114
                                · rcases p3067_3 (m.d 2 4) (by simp) with h3115 | h3115
                                  · rcases p3067_3 (m.d 2 5) (by simp) with h3116 | h3116
                                    · rcases h4bigk with h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c | h3117c
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h1, h1923, h2424, hc45, hlam, hphi, ht0b, ht5b, p3117_1, u0elo0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h1270, hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h1, h1923, h1926, h1932, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3117_1, u0elo0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        rcases p3117_3 (m.d 0 4) (by simp) with h3122 | h3122
                                        · rcases p3117_3 (m.d 1 4) (by simp) with h3123 | h3123
                                          · linarith only [h2, h3123, hlam]
                                          · linarith only [h2424, h3123, hlam]
                                        · linarith only [h3122, hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h2, hlam, p3117_1]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h1928, hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h1932, hlam, p3117_1]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p3117_1, u0elo0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h1925, h2425, hc02, hc23, hlam, hphi, p2429_1, p3117_1]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        rcases p3117_3 (m.d 0 4) (by simp) with h3133 | h3133
                                        · linarith only [h1270, h3133, hlam]
                                        · linarith only [h2, h3133, hlam]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h1926, h1932, h2425, hc12, hc23, hlam, hphi, p3117_1]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        rcases p3117_3 (m.d 0 4) (by simp) with h3138 | h3138
                                        · linarith only [h1270, h3138, hlam]
                                        · linarith only [h1925, h3138, hlam]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h1923, hlam, p3117_1]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h1, h1923, hc14, hlam, hphi, ht0b, ht45, ht5b, p3117_1, u0elo0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h2425, hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h1, h1923, hc45, hlam, hphi, ht0b, ht5b, p3117_1, u0elo0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h1925, hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h2424, hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h2427, hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [h2428, hlam, p3117_0]
                                      · have p3117_0 := h3117c.1
                                        have p3117_1 := h3117c.2.1
                                        have p3117_2 := h3117c.2.2.1
                                        have p3117_3 := h3117c.2.2.2
                                        linarith only [hlam, p3117_0]
                                    · linarith only [h3116, hlam, p3067_0]
                                  · linarith only [h1270, h3115, hlam]
                                · linarith only [h3114, h4, hlam]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            rcases p3067_3 (m.d 0 2) (by simp) with h3154 | h3154
                            · linarith only [h1799, h3154, hlam]
                            · linarith only [h0, h3154, hlam]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h2426, hlam, p3067_1]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [h2427, hlam, p3067_0]
                          · have p3067_0 := h3067c.1
                            have p3067_1 := h3067c.2.1
                            have p3067_2 := h3067c.2.2.1
                            have p3067_3 := h3067c.2.2.2
                            linarith only [hlam, p3067_0]
                      · linarith only [h1799, h2785, hlam]
                    · linarith only [h1270, h2784, hlam]
                  · linarith only [h2783, h4, hlam]
              · linarith only [h0, h2780, hlam]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1924, hlam, p2429_0]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [h1925, hlam, p2429_1]
            · have p2429_0 := h2429c.1
              have p2429_1 := h2429c.2.1
              have p2429_2 := h2429c.2.2.1
              have p2429_3 := h2429c.2.2.2
              linarith only [hlam, p2429_0]
          · linarith only [h2, h2424, h2428, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · linarith only [h0, h1270, h2424, h2427, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · linarith only [h1924, h2426, h4, hlam]
    · linarith only [h1923, h2425, h4, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h3171 | h3171
    · rcases m.htr 2 3 5 (by decide) (by decide) with h3172 | h3172
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3173 | h3173
        · rcases m.htr 3 4 5 (by decide) (by decide) with h3174 | h3174
          · linarith only [h1, h1923, h1926, h1932, h2424, h3174, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · linarith only [h1925, h1926, h1932, h3174, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
        · linarith only [h1270, h1925, h3173, hlam]
      · linarith only [h1924, h3172, h4, hlam]
    · linarith only [h1923, h3171, h4, hlam]

set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1923 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1924 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1925 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1926 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1928 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1930 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  rcases m.htr 1 3 4 (by decide) (by decide) with h1932 | h1932
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x1_x1_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924 h1925 h1926 h1928 h1930 h1932
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0_x0_x1_x1_x1_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924 h1925 h1926 h1928 h1930 h1932

end R2N4
