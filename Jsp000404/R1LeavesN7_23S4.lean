import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h2445 | h2445
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2446 | h2446
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2447 | h2447
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2448 | h2448
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2449 | h2449
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2450 | h2450
            · linarith only [h2, h2445, h2450, h4, hc12, hlam, hphi, u1ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2452 | h2452
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2453 | h2453
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2454 | h2454
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2455 | h2455
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2456 | h2456
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2457 | h2457
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2458 | h2458
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2459 | h2459
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2460 | h2460
                              · rcases h2bigk with h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c | h2461c
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h2452, h2457, h2460, hc02, hc45, hlam, hphi, ht0b, ht5b, p2461_1]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h4, hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h2457, h2460, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2461_1]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  rcases p2461_3 (m.d 0 2) (by simp) with h2466 | h2466
                                  · rcases p2461_3 (m.d 1 2) (by simp) with h2467 | h2467
                                    · linarith only [h0, h2467, hlam]
                                    · linarith only [h2453, h2467, hlam]
                                  · linarith only [h2466, hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h0, hlam, p2461_1]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h2450, hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h0, h2457, h2460, hc01, hc45, hlam, hphi, ht0b, ht5b, p2461_1]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  rcases p2461_3 (m.d 0 2) (by simp) with h2475 | h2475
                                  · rcases p2461_3 (m.d 1 2) (by simp) with h2476 | h2476
                                    · rcases p2461_3 (m.d 2 3) (by simp) with h2477 | h2477
                                      · rcases p2461_3 (m.d 2 4) (by simp) with h2478 | h2478
                                        · linarith only [h2452, h2478, hlam]
                                        · linarith only [h2459, h2478, hlam]
                                      · linarith only [h2458, h2477, hlam]
                                    · linarith only [h2476, hlam, p2461_0]
                                  · linarith only [h2446, h2475, hlam]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p2461_1, u1ehi1]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p2461_1, u1ehi1]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  rcases p2461_3 (m.d 0 2) (by simp) with h2487 | h2487
                                  · linarith only [h2487, h4, hlam]
                                  · linarith only [h2445, h2487, hlam]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  rcases p2461_3 (m.d 0 2) (by simp) with h2490 | h2490
                                  · linarith only [h2490, h4, hlam]
                                  · linarith only [h2446, h2490, hlam]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h2445, hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h2452, hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h2457, hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h0, h2452, hc01, hc25, hlam, hphi, ht0b, ht5b, p2461_1]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h2446, hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h2453, hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h2458, hlam, p2461_0]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [h2459, hlam, p2461_1]
                                · have p2461_0 := h2461c.1
                                  have p2461_1 := h2461c.2.1
                                  have p2461_2 := h2461c.2.2.1
                                  have p2461_3 := h2461c.2.2.2
                                  linarith only [hlam, p2461_0]
                              · linarith only [h0, h2452, h2459, h2460, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2504 | h2504
                              · linarith only [h2457, h2459, h2504, hlam]
                              · rcases h2bigk with h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c | h2506c
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h4, hc12, hc23, hlam, hphi, p2506_1]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h4, hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  rcases p2506_3 (m.d 0 2) (by simp) with h2510 | h2510
                                  · rcases p2506_3 (m.d 1 2) (by simp) with h2511 | h2511
                                    · linarith only [h0, h2511, hlam]
                                    · linarith only [h2452, h2511, hlam]
                                  · linarith only [h2510, hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  rcases p2506_3 (m.d 0 2) (by simp) with h2515 | h2515
                                  · rcases p2506_3 (m.d 1 2) (by simp) with h2516 | h2516
                                    · linarith only [h0, h2516, hlam]
                                    · linarith only [h2453, h2516, hlam]
                                  · linarith only [h2515, hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h0, hlam, p2506_1]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h2450, hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  rcases p2506_3 (m.d 0 2) (by simp) with h2523 | h2523
                                  · rcases p2506_3 (m.d 1 2) (by simp) with h2524 | h2524
                                    · rcases p2506_3 (m.d 2 3) (by simp) with h2525 | h2525
                                      · rcases p2506_3 (m.d 2 4) (by simp) with h2526 | h2526
                                        · linarith only [h2526, hlam, p2506_0]
                                        · rcases p2506_3 (m.d 2 5) (by simp) with h2528 | h2528
                                          · linarith only [h2453, h2528, hlam]
                                          · linarith only [h2459, h2528, hlam]
                                      · linarith only [h2457, h2525, hlam]
                                    · linarith only [h2524, hlam, p2506_0]
                                  · linarith only [h2445, h2523, hlam]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  rcases p2506_3 (m.d 0 2) (by simp) with h2534 | h2534
                                  · rcases p2506_3 (m.d 1 2) (by simp) with h2535 | h2535
                                    · rcases p2506_3 (m.d 2 3) (by simp) with h2536 | h2536
                                      · rcases p2506_3 (m.d 2 4) (by simp) with h2537 | h2537
                                        · linarith only [h2452, h2537, hlam]
                                        · rcases p2506_3 (m.d 2 5) (by simp) with h2539 | h2539
                                          · linarith only [h2539, hlam, p2506_0]
                                          · rcases h2emax with h2541 | h2541 | h2541 | h2541 | h2541
                                            · linarith only [h2, h2445, h2456, h2459, h2541, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                            · linarith only [h2452, h2456, h2459, h2541, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                            · linarith only [h1, h2541, h4, hlam, ht12, u1ehi2]
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
                                                linarith only [h2445, h2456, h2457, h2459, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2545_1]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                rcases p2545_3 (m.d 0 4) (by simp) with h2548 | h2548
                                                · rcases p2545_3 (m.d 1 4) (by simp) with h2549 | h2549
                                                  · linarith only [h2, h2549, hlam]
                                                  · linarith only [h2452, h2549, hlam]
                                                · linarith only [h2445, h2548, hlam]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                rcases p2545_3 (m.d 0 4) (by simp) with h2553 | h2553
                                                · rcases p2545_3 (m.d 1 4) (by simp) with h2554 | h2554
                                                  · linarith only [h2, h2554, hlam]
                                                  · linarith only [h2454, h2554, hlam]
                                                · linarith only [h2447, h2553, hlam]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2445, h2457, h2459, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2545_1]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2, hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                rcases p2545_3 (m.d 0 4) (by simp) with h2561 | h2561
                                                · rcases p2545_3 (m.d 1 4) (by simp) with h2562 | h2562
                                                  · rcases p2545_3 (m.d 2 4) (by simp) with h2563 | h2563
                                                    · linarith only [h2452, h2563, hlam]
                                                    · rcases p2545_3 (m.d 3 4) (by simp) with h2565 | h2565
                                                      · linarith only [h2454, h2565, hlam]
                                                      · rcases p2545_3 (m.d 4 5) (by simp) with h2567 | h2567
                                                        · linarith only [h2456, h2567, hlam]
                                                        · linarith only [h2459, h2567, hlam]
                                                  · linarith only [h2452, h2562, hlam]
                                                · linarith only [h2445, h2561, hlam]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                rcases p2545_3 (m.d 0 4) (by simp) with h2572 | h2572
                                                · rcases p2545_3 (m.d 1 4) (by simp) with h2573 | h2573
                                                  · rcases p2545_3 (m.d 2 4) (by simp) with h2574 | h2574
                                                    · linarith only [h2452, h2574, hlam]
                                                    · linarith only [h2457, h2574, hlam]
                                                  · linarith only [h2454, h2573, hlam]
                                                · linarith only [h2447, h2572, hlam]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h0, h2452, h2457, h2459, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2545_1]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2445, hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2452, hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2459, hc34, hc45, hlam, hphi, p2545_1]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2459, hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2447, hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2454, hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2457, hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2504, hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2449, hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2456, hlam, p2545_0]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h2445, h2449, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2545_1]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [h0, h2452, h2456, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2545_1]
                                              · have p2545_0 := h2545c.1
                                                have p2545_1 := h2545c.2.1
                                                have p2545_2 := h2545c.2.2.1
                                                have p2545_3 := h2545c.2.2.2
                                                linarith only [hlam, p2545_0]
                                            · rcases h4bigk with h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2445, h2456, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2595_1]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                rcases p2595_3 (m.d 0 4) (by simp) with h2598 | h2598
                                                · rcases p2595_3 (m.d 1 4) (by simp) with h2599 | h2599
                                                  · linarith only [h2, h2599, hlam]
                                                  · linarith only [h2452, h2599, hlam]
                                                · linarith only [h2445, h2598, hlam]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                rcases p2595_3 (m.d 0 4) (by simp) with h2603 | h2603
                                                · rcases p2595_3 (m.d 1 4) (by simp) with h2604 | h2604
                                                  · linarith only [h2, h2604, hlam]
                                                  · linarith only [h2454, h2604, hlam]
                                                · linarith only [h2447, h2603, hlam]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2445, h2457, h2459, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2595_1]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2, hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                rcases p2595_3 (m.d 0 4) (by simp) with h2611 | h2611
                                                · rcases p2595_3 (m.d 1 4) (by simp) with h2612 | h2612
                                                  · rcases p2595_3 (m.d 2 4) (by simp) with h2613 | h2613
                                                    · linarith only [h2452, h2613, hlam]
                                                    · rcases p2595_3 (m.d 3 4) (by simp) with h2615 | h2615
                                                      · linarith only [h2454, h2615, hlam]
                                                      · rcases p2595_3 (m.d 4 5) (by simp) with h2617 | h2617
                                                        · linarith only [h2456, h2617, hlam]
                                                        · linarith only [h2459, h2617, hlam]
                                                  · linarith only [h2452, h2612, hlam]
                                                · linarith only [h2445, h2611, hlam]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                rcases p2595_3 (m.d 0 4) (by simp) with h2622 | h2622
                                                · rcases p2595_3 (m.d 1 4) (by simp) with h2623 | h2623
                                                  · rcases p2595_3 (m.d 2 4) (by simp) with h2624 | h2624
                                                    · linarith only [h2452, h2624, hlam]
                                                    · linarith only [h2457, h2624, hlam]
                                                  · linarith only [h2454, h2623, hlam]
                                                · linarith only [h2447, h2622, hlam]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2, h2457, h2459, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2595_1]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2445, hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2452, hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2459, hc34, hc45, hlam, hphi, p2595_1]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2459, hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2447, hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2454, hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2457, hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2504, hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2449, hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2456, hlam, p2595_0]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2445, h2449, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2595_1]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [h2, h2445, h2456, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2595_1]
                                              · have p2595_0 := h2595c.1
                                                have p2595_1 := h2595c.2.1
                                                have p2595_2 := h2595c.2.2.1
                                                have p2595_3 := h2595c.2.2.2
                                                linarith only [hlam, p2595_0]
                                      · linarith only [h2458, h2536, hlam]
                                    · linarith only [h2535, hlam, p2506_0]
                                  · linarith only [h2446, h2534, hlam]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p2506_1, u1ehi1]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p2506_1, u1ehi1]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h0, h2452, h2456, h2459, h4, hlam, p2506_2]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  rcases p2506_3 (m.d 0 2) (by simp) with h2652 | h2652
                                  · linarith only [h2652, h4, hlam]
                                  · linarith only [h2446, h2652, hlam]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h2445, hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h2452, hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h2457, hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h2459, hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h2446, hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h2453, hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h2458, hlam, p2506_0]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [h2446, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2506_1]
                                · have p2506_0 := h2506c.1
                                  have p2506_1 := h2506c.2.1
                                  have p2506_2 := h2506c.2.2.1
                                  have p2506_3 := h2506c.2.2.2
                                  linarith only [hlam, p2506_0]
                          · linarith only [h0, h2458, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h2445, h2449, h2457, h3, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                      · linarith only [h2445, h2449, h2456, h4, hc23, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h2445, h2448, h2449, h2455, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h2447, h2450, h2454, h4, hc23, hlam, hphi, ht12, u1ehi1]
                · linarith only [h2446, h2452, h2453, h4, hc23, hlam, hphi, ht12, u1ehi3]
              · linarith only [h2445, h2452, h4, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2672 | h2672
            · linarith only [h0, h2445, h2672, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2674 | h2674
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2675 | h2675
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2676 | h2676
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2677 | h2677
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2678 | h2678
                      · linarith only [h2, h2449, h2678, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2680 | h2680
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2681 | h2681
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2682 | h2682
                            · linarith only [h2, h2449, h2674, h2682, hc12, hlam, hphi, u1ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2684 | h2684
                              · linarith only [h0, h2, h2449, h2675, h2680, h2682, h2684, h4, hc23, hlam, hphi, ht12, u1ehi3]
                              · rcases h2bigk with h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h4, hc12, hc23, hlam, hphi, p2686_1]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h4, hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  rcases p2686_3 (m.d 0 2) (by simp) with h2690 | h2690
                                  · rcases p2686_3 (m.d 1 2) (by simp) with h2691 | h2691
                                    · linarith only [h0, h2691, hlam]
                                    · linarith only [h2674, h2691, hlam]
                                  · linarith only [h2690, hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  rcases p2686_3 (m.d 0 2) (by simp) with h2695 | h2695
                                  · rcases p2686_3 (m.d 1 2) (by simp) with h2696 | h2696
                                    · linarith only [h0, h2696, hlam]
                                    · linarith only [h2675, h2696, hlam]
                                  · linarith only [h2695, hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h0, hlam, p2686_1]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h2672, hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  rcases p2686_3 (m.d 0 2) (by simp) with h2703 | h2703
                                  · rcases p2686_3 (m.d 1 2) (by simp) with h2704 | h2704
                                    · rcases p2686_3 (m.d 2 3) (by simp) with h2705 | h2705
                                      · rcases p2686_3 (m.d 2 4) (by simp) with h2706 | h2706
                                        · linarith only [h2706, hlam, p2686_0]
                                        · rcases p2686_3 (m.d 2 5) (by simp) with h2708 | h2708
                                          · linarith only [h2675, h2708, hlam]
                                          · linarith only [h2682, h2708, hlam]
                                      · linarith only [h2680, h2705, hlam]
                                    · linarith only [h2704, hlam, p2686_0]
                                  · linarith only [h2445, h2703, hlam]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  rcases p2686_3 (m.d 0 2) (by simp) with h2714 | h2714
                                  · rcases p2686_3 (m.d 1 2) (by simp) with h2715 | h2715
                                    · rcases p2686_3 (m.d 2 3) (by simp) with h2716 | h2716
                                      · rcases p2686_3 (m.d 2 4) (by simp) with h2717 | h2717
                                        · linarith only [h2674, h2717, hlam]
                                        · rcases p2686_3 (m.d 2 5) (by simp) with h2719 | h2719
                                          · linarith only [h2719, hlam, p2686_0]
                                          · rcases h2emax with h2721 | h2721 | h2721 | h2721 | h2721
                                            · linarith only [h0, h2680, h2682, h2721, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2686_1]
                                            · linarith only [h2680, h2682, h2721, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2686_1]
                                            · linarith only [h1, h2721, h4, hlam, ht12, u1ehi2]
                                            · rcases h4bigk with h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2449, hc45, hlam, hphi, ht12, ht23, ht34, p2725_1, u1ehi3]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2449, h2680, hc34, hc45, hlam, hphi, p2725_1]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2449, hc34, hc45, hlam, hphi, p2725_1]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2449, hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2, hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2, h2449, h2680, hc34, hc45, hlam, hphi, p2725_1]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2, h2449, hc34, hc45, hlam, hphi, p2725_1]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2678, hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2445, hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2674, hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h0, h2682, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2686_1, p2725_1]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2682, hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2447, hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2676, hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2680, hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2684, hlam, p2725_0]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h2, hc45, hlam, hphi, ht12, ht23, ht34, p2725_1, u1ehi3]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [h0, h2682, h4, hc23, hc24, hc45, hlam, hphi, ht12, p2686_1, p2725_1, u1ehi3]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                rcases p2725_3 (m.d 0 4) (by simp) with h2748 | h2748
                                                · linarith only [h2449, h2748, hlam]
                                                · linarith only [h2445, h2748, hlam]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                rcases p2725_3 (m.d 0 4) (by simp) with h2751 | h2751
                                                · linarith only [h2449, h2751, hlam]
                                                · linarith only [h2447, h2751, hlam]
                                              · have p2725_0 := h2725c.1
                                                have p2725_1 := h2725c.2.1
                                                have p2725_2 := h2725c.2.2.1
                                                have p2725_3 := h2725c.2.2.2
                                                linarith only [hlam, p2725_0]
                                            · rcases h4bigk with h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2445, h4, hc23, hlam, hphi, ht12, p2755_1, u1ehi3]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2449, h2680, hc34, hc45, hlam, hphi, p2755_1]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2449, hc34, hc45, hlam, hphi, p2755_1]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2449, hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2, hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2, h2449, h2680, hc34, hc45, hlam, hphi, p2755_1]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2, h2449, hc34, hc45, hlam, hphi, p2755_1]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2678, hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2445, hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2674, hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h0, h2682, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2686_1, p2755_1]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2682, hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2447, hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2676, hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2680, hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2684, hlam, p2755_0]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h2, hc45, hlam, hphi, ht12, ht23, ht34, p2755_1, u1ehi3]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [h0, h2682, h4, hc23, hc24, hc45, hlam, hphi, ht12, p2686_1, p2755_1, u1ehi3]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                rcases p2755_3 (m.d 0 4) (by simp) with h2778 | h2778
                                                · linarith only [h2449, h2778, hlam]
                                                · linarith only [h2445, h2778, hlam]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                rcases p2755_3 (m.d 0 4) (by simp) with h2781 | h2781
                                                · linarith only [h2449, h2781, hlam]
                                                · linarith only [h2447, h2781, hlam]
                                              · have p2755_0 := h2755c.1
                                                have p2755_1 := h2755c.2.1
                                                have p2755_2 := h2755c.2.2.1
                                                have p2755_3 := h2755c.2.2.2
                                                linarith only [hlam, p2755_0]
                                      · linarith only [h2681, h2716, hlam]
                                    · linarith only [h2715, hlam, p2686_0]
                                  · linarith only [h2446, h2714, hlam]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p2686_1, u1ehi1]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p2686_1, u1ehi1]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  rcases p2686_3 (m.d 0 2) (by simp) with h2791 | h2791
                                  · linarith only [h2791, h4, hlam]
                                  · linarith only [h2445, h2791, hlam]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  rcases p2686_3 (m.d 0 2) (by simp) with h2794 | h2794
                                  · linarith only [h2794, h4, hlam]
                                  · linarith only [h2446, h2794, hlam]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h2445, hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h2674, hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h2680, hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h2682, hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h2446, hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h2675, hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h2681, hlam, p2686_0]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [h2446, h2680, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2686_1]
                                · have p2686_0 := h2686c.1
                                  have p2686_1 := h2686c.2.1
                                  have p2686_2 := h2686c.2.2.1
                                  have p2686_3 := h2686c.2.2.2
                                  linarith only [hlam, p2686_0]
                          · linarith only [h1, h2677, h2681, h4, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h0, h2680, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h2448, h2672, h2675, h2677, h4, hc23, hlam, hphi, ht12, u1ehi4]
                  · linarith only [h2447, h2672, h2675, h2676, h4, hc23, hlam, hphi, ht12, u1ehi4]
                · linarith only [h2446, h2674, h2675, h4, hc23, hlam, hphi, ht12, u1ehi3]
              · linarith only [h2445, h2674, h4, hc12, hc23, hlam, hphi]
        · linarith only [h2446, h2448, h4, hlam]
      · linarith only [h2445, h2447, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2815 | h2815
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2816 | h2816
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2817 | h2817
          · linarith only [h2445, h2446, h2817, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2819 | h2819
            · linarith only [h0, h2445, h2819, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2821 | h2821
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2822 | h2822
                · linarith only [h2, h2445, h2446, h2822, hc12, hlam, hphi, u1ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2824 | h2824
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2825 | h2825
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2826 | h2826
                      · linarith only [h2, h2817, h2826, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2828 | h2828
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2829 | h2829
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2830 | h2830
                            · linarith only [h2, h2817, h2830, hc24, hlam, hphi, ht12, u1ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2832 | h2832
                              · linarith only [h2, h2445, h2446, h2830, h2832, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · rcases h2bigk with h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2446, h2829, hc12, hc23, hlam, hphi, p2834_1]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h4, hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2446, h2828, h2830, hc34, hc45, hlam, hphi, p2834_1]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2446, hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h0, hlam, p2834_1]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2819, hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h0, h2446, h2828, h2830, hc34, hc45, hlam, hphi, p2834_1]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2822, hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p2834_1, u1ehi1]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p2834_1, u1ehi1]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  rcases p2834_3 (m.d 0 2) (by simp) with h2848 | h2848
                                  · linarith only [h2848, h4, hlam]
                                  · linarith only [h2445, h2848, hlam]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2, h2445, h2446, hc23, hlam, hphi, ht12, p2834_1, u1ehi3]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2445, hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2821, hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2828, hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2830, hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2, h2445, hc25, hlam, hphi, ht12, p2834_1, u1ehi3]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2821, hc25, hlam, hphi, ht12, p2834_1, u1ehi3]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [h2829, hlam, p2834_0]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  rcases p2834_3 (m.d 0 2) (by simp) with h2860 | h2860
                                  · linarith only [h2446, h2860, hlam]
                                  · linarith only [h2445, h2860, hlam]
                                · have p2834_0 := h2834c.1
                                  have p2834_1 := h2834c.2.1
                                  have p2834_2 := h2834c.2.2.1
                                  have p2834_3 := h2834c.2.2.2
                                  linarith only [hlam, p2834_0]
                          · linarith only [h1, h2, h2445, h2825, h2829, h4, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                        · linarith only [h2, h2445, h2828, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · linarith only [h2816, h2825, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h2815, h2819, h2821, h2824, h4, hc23, hlam, hphi, ht12, u1ehi3]
              · linarith only [h2445, h2821, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2869 | h2869
          · linarith only [h2445, h2446, h2869, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2871 | h2871
            · linarith only [h2, h2445, h2871, h4, hc12, hlam, hphi, u1ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2873 | h2873
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2874 | h2874
                · linarith only [h2, h2445, h2446, h2874, hc12, hlam, hphi, u1ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2876 | h2876
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2877 | h2877
                    · linarith only [h1, h2816, h2877, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2879 | h2879
                      · linarith only [h2, h2869, h2879, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2881 | h2881
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2882 | h2882
                          · linarith only [h1, h2816, h2882, hc23, hlam, hphi, ht12, u1ehi2]
                          · linarith only [h2, h2445, h2882, h4, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h2, h2445, h2881, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                  · linarith only [h2815, h2871, h2876, h4, hc23, hlam, hphi, ht12, u1ehi1]
              · linarith only [h2445, h2873, h4, hc23, hlam, hphi, ht12, u1ehi1]
      · linarith only [h2445, h2815, h4, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2889 | h2889
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2890 | h2890
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2891 | h2891
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2892 | h2892
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2893 | h2893
            · linarith only [h2889, h2893, h3, h4, hc12, hlam, hphi, u1ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2895 | h2895
              · linarith only [h0, h2445, h2895, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2897 | h2897
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2898 | h2898
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2899 | h2899
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2900 | h2900
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2901 | h2901
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2902 | h2902
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2903 | h2903
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2904 | h2904
                              · rcases h2bigk with h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c | h2905c
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2445, h2901, hc12, hc23, hlam, hphi, p2905_1]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h4, hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2445, hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  rcases p2905_3 (m.d 0 2) (by simp) with h2910 | h2910
                                  · rcases p2905_3 (m.d 1 2) (by simp) with h2911 | h2911
                                    · linarith only [h0, h2911, hlam]
                                    · linarith only [h2897, h2911, hlam]
                                  · linarith only [h2910, hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h0, hlam, p2905_1]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2893, hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2895, hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  rcases p2905_3 (m.d 0 2) (by simp) with h2919 | h2919
                                  · rcases p2905_3 (m.d 1 2) (by simp) with h2920 | h2920
                                    · rcases p2905_3 (m.d 2 3) (by simp) with h2921 | h2921
                                      · rcases p2905_3 (m.d 2 4) (by simp) with h2922 | h2922
                                        · rcases p2905_3 (m.d 2 5) (by simp) with h2923 | h2923
                                          · linarith only [h2923, hlam, p2905_0]
                                          · rcases h2emax with h2925 | h2925 | h2925 | h2925 | h2925
                                            · linarith only [h0, h2902, h2904, h2925, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2905_1]
                                            · linarith only [h2902, h2904, h2925, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2905_1]
                                            · linarith only [h1, h2895, h2898, h2902, h2904, h2925, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2905_1]
                                            · linarith only [h0, h2445, h2902, h2904, h2925, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2905_1]
                                            · rcases h4bigk with h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c | h2930c
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2890, h2895, h2902, h2904, hc03, hc45, hlam, hphi, ht0b, ht5b, p2905_1, p2930_1]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2445, hlam, p2930_1]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                rcases p2930_3 (m.d 0 4) (by simp) with h2934 | h2934
                                                · rcases p2930_3 (m.d 1 4) (by simp) with h2935 | h2935
                                                  · linarith only [h2, h2935, hlam]
                                                  · linarith only [h2898, h2935, hlam]
                                                · linarith only [h2890, h2934, hlam]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                rcases p2930_3 (m.d 0 4) (by simp) with h2939 | h2939
                                                · rcases p2930_3 (m.d 1 4) (by simp) with h2940 | h2940
                                                  · linarith only [h2, h2940, hlam]
                                                  · linarith only [h2900, h2940, hlam]
                                                · linarith only [h2939, hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2, hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2895, hlam, p2930_1]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h1, h2898, h2904, hc01, hc45, hlam, hphi, ht0b, ht5b, p2930_1]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                rcases p2930_3 (m.d 0 4) (by simp) with h2948 | h2948
                                                · rcases p2930_3 (m.d 1 4) (by simp) with h2949 | h2949
                                                  · rcases p2930_3 (m.d 2 4) (by simp) with h2950 | h2950
                                                    · rcases p2930_3 (m.d 3 4) (by simp) with h2951 | h2951
                                                      · linarith only [h2898, h2951, hlam]
                                                      · linarith only [h2904, h2951, hlam]
                                                    · linarith only [h2903, h2950, hlam]
                                                  · linarith only [h2949, hlam, p2930_0]
                                                · linarith only [h2892, h2948, hlam]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2, hc24, hlam, hphi, ht12, p2930_1, u1ehi3]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [hc24, hlam, hphi, ht12, p2930_1, u1ehi3]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                rcases p2930_3 (m.d 0 4) (by simp) with h2960 | h2960
                                                · linarith only [h2445, h2960, hlam]
                                                · linarith only [h2890, h2960, hlam]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h0, h2445, h2902, h2904, hlam, p2905_1, p2930_2]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2890, hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2898, hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2901, hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h1, h2898, hc01, hc45, hlam, hphi, ht0b, ht5b, p2930_1]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2892, hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2900, hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2903, hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [h2904, hlam, p2930_0]
                                              · have p2930_0 := h2930c.1
                                                have p2930_1 := h2930c.2.1
                                                have p2930_2 := h2930c.2.2.1
                                                have p2930_3 := h2930c.2.2.2
                                                linarith only [hlam, p2930_0]
                                        · linarith only [h2903, h2922, hlam]
                                      · linarith only [h2902, h2921, hlam]
                                    · linarith only [h2920, hlam, p2905_0]
                                  · linarith only [h2889, h2919, hlam]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p2905_1, u1ehi1]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p2905_1, u1ehi1]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2445, h2889, h3, hc23, hlam, hphi, ht12, p2905_1, u1ehi4]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  rcases p2905_3 (m.d 0 2) (by simp) with h2982 | h2982
                                  · linarith only [h2982, h4, hlam]
                                  · linarith only [h2889, h2982, hlam]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2889, h3, hc24, hlam, hphi, ht12, p2905_1, u1ehi4]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2897, hc24, hlam, hphi, ht12, p2905_1, u1ehi4]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2901, hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  rcases p2905_3 (m.d 0 2) (by simp) with h2989 | h2989
                                  · linarith only [h2445, h2989, hlam]
                                  · linarith only [h2889, h2989, hlam]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2889, hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2897, hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2902, hlam, p2905_0]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [h2903, hlam, p2905_1]
                                · have p2905_0 := h2905c.1
                                  have p2905_1 := h2905c.2.1
                                  have p2905_2 := h2905c.2.2.1
                                  have p2905_3 := h2905c.2.2.2
                                  linarith only [hlam, p2905_0]
                              · rcases h2bigk with h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c | h2997c
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2445, h2897, h2901, h2903, h2904, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2997_1]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h4, hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2445, hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2445, h2901, h2903, h2904, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2997_1]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h0, hlam, p2997_1]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2893, hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2895, hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h0, h2903, h2904, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2997_1]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p2997_1, u1ehi1]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p2997_1, u1ehi1]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2, h2445, hc23, hlam, hphi, ht12, p2997_1, u1ehi3]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  rcases p2997_3 (m.d 0 2) (by simp) with h3012 | h3012
                                  · linarith only [h3012, h4, hlam]
                                  · linarith only [h2889, h3012, hlam]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h0, h2897, h2903, h2904, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2997_1]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2897, h2903, h2904, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2997_1]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2901, hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  rcases p2997_3 (m.d 0 2) (by simp) with h3019 | h3019
                                  · linarith only [h2445, h3019, hlam]
                                  · linarith only [h2889, h3019, hlam]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2889, hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2897, hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2902, hlam, p2997_0]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [h2903, hlam, p2997_1]
                                · have p2997_0 := h2997c.1
                                  have p2997_1 := h2997c.2.1
                                  have p2997_2 := h2997c.2.2.1
                                  have p2997_3 := h2997c.2.2.2
                                  linarith only [hlam, p2997_0]
                            · linarith only [h0, h2445, h2903, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                          · linarith only [h2889, h2902, h3, h4, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                        · linarith only [h2889, h2901, h3, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                      · linarith only [h2445, h2892, h2900, hc24, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h2891, h2899, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h2890, h2893, h2897, h2898, h4, hc23, hlam, hphi, ht12, u1ehi4]
                · linarith only [h2889, h2897, h4, hc12, hc23, hlam, hphi]
          · linarith only [h2445, h2889, h2892, hlam]
        · linarith only [h2889, h2891, h4, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3036 | h3036
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3037 | h3037
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3038 | h3038
            · linarith only [h0, h2889, h3038, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3040 | h3040
              · linarith only [h2445, h2889, h3, h3040, hc12, hlam, hphi, u1ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3042 | h3042
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3043 | h3043
                  · linarith only [h1, h2890, h3043, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3045 | h3045
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3046 | h3046
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3047 | h3047
                        · linarith only [h1, h2890, h3047, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h2889, h3, h3047, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                      · linarith only [h2445, h3037, h3038, h3042, h3043, h3046, hc24, hlam, hphi, ht12, u1ehi4]
                    · linarith only [h3036, h3038, h3042, h3045, h4, hc23, hlam, hphi, ht12, u1ehi4]
                · linarith only [h2889, h3042, h4, hc12, hc23, hlam, hphi]
          · linarith only [h2889, h2890, h3037, h4, hlam]
        · linarith only [h2889, h3036, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3055 | h3055
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3056 | h3056
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3057 | h3057
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3058 | h3058
            · linarith only [h0, h3058, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3060 | h3060
              · linarith only [h0, h2445, h3060, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3062 | h3062
                · linarith only [h0, h2889, h3062, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3064 | h3064
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3065 | h3065
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3066 | h3066
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3067 | h3067
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3068 | h3068
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3069 | h3069
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3070 | h3070
                              · rcases h2bigk with h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c | h3071c
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h2889, h3067, h3069, hc12, hc23, hlam, hphi, p3071_1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h4, hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h2445, hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h2889, hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h0, hlam, p3071_1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h3058, hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h3060, hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h3062, hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p3071_1, u1ehi1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p3071_1, u1ehi1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h0, h2445, hc23, hlam, hphi, ht12, p3071_1, u1ehi1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h0, h2889, hc23, hlam, hphi, ht12, p3071_1, u1ehi1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h0, hc24, hlam, hphi, ht12, p3071_1, u1ehi1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht12, p3071_1, u1ehi1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h3067, hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h0, h2889, h3067, hc23, hlam, hphi, ht12, p3071_1, u1ehi1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h0, hc25, hlam, hphi, ht12, p3071_1, u1ehi1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht12, p3071_1, u1ehi1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h3068, hlam, p3071_0]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [h3069, hlam, p3071_1]
                                · have p3071_0 := h3071c.1
                                  have p3071_1 := h3071c.2.1
                                  have p3071_2 := h3071c.2.2.1
                                  have p3071_3 := h3071c.2.2.2
                                  linarith only [hlam, p3071_0]
                              · rcases h2bigk with h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c | h3097c
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h4, hc23, hlam, hphi, ht12, p3097_1, u1ehi1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h4, hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h2445, hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h2889, hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h0, hlam, p3097_1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h3058, hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h3060, hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h3062, hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h0, hc23, hlam, hphi, ht12, p3097_1, u1ehi1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht12, p3097_1, u1ehi1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h0, h2445, hc23, hlam, hphi, ht12, p3097_1, u1ehi1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h0, h2889, hc23, hlam, hphi, ht12, p3097_1, u1ehi1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h0, hc24, hlam, hphi, ht12, p3097_1, u1ehi1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht12, p3097_1, u1ehi1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h3067, hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h0, h2889, h3067, hc23, hlam, hphi, ht12, p3097_1, u1ehi1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h0, hc25, hlam, hphi, ht12, p3097_1, u1ehi1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht12, p3097_1, u1ehi1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h3068, hlam, p3097_0]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [h3069, hlam, p3097_1]
                                · have p3097_0 := h3097c.1
                                  have p3097_1 := h3097c.2.1
                                  have p3097_2 := h3097c.2.2.1
                                  have p3097_3 := h3097c.2.2.2
                                  linarith only [hlam, p3097_0]
                            · linarith only [h0, h1, h2445, h3064, h3066, h3069, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                          · linarith only [h0, h3068, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h0, h3067, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h2445, h3057, h3066, hc24, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h3056, h3065, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h3055, h3058, h3064, h4, hc23, hlam, hphi, ht12, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3129 | h3129
            · linarith only [h0, h3129, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3131 | h3131
              · linarith only [h0, h2445, h3131, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3133 | h3133
                · linarith only [h0, h2889, h3133, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3135 | h3135
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3136 | h3136
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3137 | h3137
                      · linarith only [h2, h3057, h3137, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3139 | h3139
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3140 | h3140
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3141 | h3141
                            · linarith only [h0, h2445, h3057, h3139, h3141, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h0, h2445, h3141, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                          · linarith only [h0, h1, h3136, h3140, h4, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                        · linarith only [h0, h3135, h3139, h4, hc14, hlam, hphi, u1ehi1]
                    · linarith only [h3056, h3136, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h3055, h3129, h3135, h4, hc23, hlam, hphi, ht12, u1ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3148 | h3148
          · linarith only [h3055, h3056, h3148, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3150 | h3150
            · linarith only [h0, h3150, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3152 | h3152
              · linarith only [h0, h2445, h3152, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3154 | h3154
                · linarith only [h0, h2889, h3154, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3156 | h3156
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3157 | h3157
                    · linarith only [h1, h3056, h3157, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3159 | h3159
                      · linarith only [h2, h3148, h3159, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3161 | h3161
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3162 | h3162
                          · linarith only [h2, h3055, h3056, h3152, h3162, hc23, hlam, hphi, ht12, u1ehi1]
                          · linarith only [h0, h3162, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h0, h3156, h3161, h4, hc13, hlam, hphi, u1ehi1]
                  · linarith only [h3055, h3156, h4, hc23, hlam, hphi, ht12, u1ehi2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3167 | h3167
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3168 | h3168
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3169 | h3169
            · linarith only [h0, h3169, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3171 | h3171
              · linarith only [h0, h2445, h3171, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3173 | h3173
                · linarith only [h0, h2889, h3173, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3175 | h3175
                  · linarith only [h0, h2889, h3055, h3167, h3175, hc13, hlam, hphi, u1ehi1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3177 | h3177
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3178 | h3178
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3179 | h3179
                        · linarith only [h0, h2889, h3055, h3167, h3179, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h0, h3179, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h2445, h3168, h3178, hc24, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h3055, h3167, h3177, hc13, hc34, hlam, hphi]
          · linarith only [h3055, h3167, h3168, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3185 | h3185
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3186 | h3186
            · linarith only [h0, h3186, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3188 | h3188
              · linarith only [h0, h2445, h3188, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3190 | h3190
                · linarith only [h0, h2889, h3190, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3192 | h3192
                  · linarith only [h0, h3055, h3192, h4, hc13, hlam, hphi, u1ehi1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3194 | h3194
                    · linarith only [h0, h3167, h3194, h4, hc13, hlam, hphi, u1ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3196 | h3196
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3197 | h3197
                        · linarith only [h0, h3055, h3197, h4, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h0, h3197, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h2445, h3185, h3196, hc24, hlam, hphi, ht12, u1ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3201 | h3201
            · linarith only [h0, h3201, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3203 | h3203
              · linarith only [h0, h2445, h3203, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3205 | h3205
                · linarith only [h0, h2889, h3205, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3207 | h3207
                  · linarith only [h0, h1, h3055, h3207, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3209 | h3209
                    · linarith only [h0, h3167, h3209, h4, hc13, hlam, hphi, u1ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3211 | h3211
                      · linarith only [h2, h3185, h3211, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3213 | h3213
                        · linarith only [h0, h3055, h3213, h4, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h0, h3213, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 6428000 in
set_option maxHeartbeats 6428000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s2 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3 m hb1 hb2 hb4 hb5 h0 h1 h2 h3
  · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]

set_option maxHeartbeats 6432000 in
set_option maxHeartbeats 6432000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s2 m hb1 hb2 hb4 hb5 h0 h1 h2
  · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]

set_option maxHeartbeats 6436000 in
set_option maxHeartbeats 6436000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s1 m hb1 hb2 hb4 hb5 h0 h1
  · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]

end R2N4
