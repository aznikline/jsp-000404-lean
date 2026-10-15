import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h2451 | h2451
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2452 | h2452
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2453 | h2453
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2454 | h2454
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2455 | h2455
          · linarith only [h1, h2455, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2457 | h2457
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2458 | h2458
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2459 | h2459
                · linarith only [h1, h2457, h2459, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2461 | h2461
                  · linarith only [h0, h2453, h2459, h2461, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h1, h2457, h2461, h7, hc23, hc34, hlam, hphi]
              · linarith only [h2451, h2455, h2457, h2458, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2465 | h2465
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2466 | h2466
                · linarith only [h0, h2, h2465, h2466, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2468 | h2468
                  · linarith only [h2452, h2457, h2468, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2470 | h2470
                    · linarith only [h0, h2453, h2470, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2472 | h2472
                      · rcases h1bigk with h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c | h2473c
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h2453, h2465, h2466, h2470, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2473_1]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          rcases p2473_3 (m.d 0 1) (by simp) with h2476 | h2476
                          · rcases p2473_3 (m.d 1 2) (by simp) with h2477 | h2477
                            · linarith only [h0, h2477, hlam]
                            · linarith only [h2452, h2477, hlam]
                          · linarith only [h2476, hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h2465, h2466, h2470, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2473_1]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          rcases p2473_3 (m.d 0 1) (by simp) with h2482 | h2482
                          · rcases p2473_3 (m.d 1 2) (by simp) with h2483 | h2483
                            · linarith only [h0, h2483, hlam]
                            · linarith only [h2454, h2483, hlam]
                          · linarith only [h2482, hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h0, hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          rcases p2473_3 (m.d 0 1) (by simp) with h2489 | h2489
                          · rcases p2473_3 (m.d 1 2) (by simp) with h2490 | h2490
                            · rcases p2473_3 (m.d 1 3) (by simp) with h2491 | h2491
                              · linarith only [h2452, h2491, hlam]
                              · rcases p2473_3 (m.d 1 4) (by simp) with h2493 | h2493
                                · linarith only [h2453, h2493, hlam]
                                · linarith only [h2455, h2493, hlam]
                            · linarith only [h2452, h2490, hlam]
                          · linarith only [h1, h2489, hlam]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h0, h2465, h2466, h2470, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2473_1]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h0, h2465, h2466, h2470, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2473_1]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h1, hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h2452, hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h2455, hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h2457, hlam, p2473_1]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h2, hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h2453, hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          rcases p2473_3 (m.d 0 1) (by simp) with h2507 | h2507
                          · rcases p2473_3 (m.d 1 2) (by simp) with h2508 | h2508
                            · rcases p2473_3 (m.d 1 3) (by simp) with h2509 | h2509
                              · linarith only [h2455, h2509, hlam]
                              · rcases p2473_3 (m.d 1 4) (by simp) with h2511 | h2511
                                · rcases p2473_3 (m.d 1 5) (by simp) with h2512 | h2512
                                  · linarith only [h2465, h2512, hlam]
                                  · linarith only [h2457, h2512, hlam]
                                · linarith only [h2455, h2511, hlam]
                            · linarith only [h2452, h2508, hlam]
                          · linarith only [h1, h2507, hlam]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h2, h2465, h2466, h2470, h7, hc23, hc34, hlam, hphi, p2473_1]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h3, hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h2454, hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          rcases p2473_3 (m.d 0 1) (by simp) with h2522 | h2522
                          · rcases p2473_3 (m.d 1 2) (by simp) with h2523 | h2523
                            · rcases p2473_3 (m.d 1 3) (by simp) with h2524 | h2524
                              · linarith only [h2457, h2524, hlam]
                              · rcases p2473_3 (m.d 1 4) (by simp) with h2526 | h2526
                                · rcases p2473_3 (m.d 1 5) (by simp) with h2527 | h2527
                                  · rcases h2bigk with h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c | h2528c
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h0, h2453, h2465, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2473_1, p2528_1]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      rcases p2528_3 (m.d 0 2) (by simp) with h2531 | h2531
                                      · rcases p2528_3 (m.d 1 2) (by simp) with h2532 | h2532
                                        · linarith only [h0, h2532, hlam]
                                        · linarith only [h2452, h2532, hlam]
                                      · linarith only [h2531, hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      rcases p2528_3 (m.d 0 2) (by simp) with h2536 | h2536
                                      · rcases p2528_3 (m.d 1 2) (by simp) with h2537 | h2537
                                        · linarith only [h0, h2537, hlam]
                                        · linarith only [h2453, h2537, hlam]
                                      · linarith only [h2536, hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      rcases p2528_3 (m.d 0 2) (by simp) with h2541 | h2541
                                      · rcases p2528_3 (m.d 1 2) (by simp) with h2542 | h2542
                                        · linarith only [h0, h2542, hlam]
                                        · linarith only [h2454, h2542, hlam]
                                      · linarith only [h2541, hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h0, hlam, p2528_1]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      rcases p2528_3 (m.d 0 2) (by simp) with h2548 | h2548
                                      · rcases p2528_3 (m.d 1 2) (by simp) with h2549 | h2549
                                        · rcases p2528_3 (m.d 2 3) (by simp) with h2550 | h2550
                                          · linarith only [h2550, hlam, p2528_0]
                                          · rcases p2528_3 (m.d 2 4) (by simp) with h2552 | h2552
                                            · linarith only [h2453, h2552, hlam]
                                            · linarith only [h2466, h2552, hlam]
                                        · linarith only [h2549, hlam, p2528_0]
                                      · linarith only [h2548, h4, hlam]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      rcases p2528_3 (m.d 0 2) (by simp) with h2557 | h2557
                                      · rcases p2528_3 (m.d 1 2) (by simp) with h2558 | h2558
                                        · rcases p2528_3 (m.d 2 3) (by simp) with h2559 | h2559
                                          · linarith only [h2452, h2559, hlam]
                                          · rcases p2528_3 (m.d 2 4) (by simp) with h2561 | h2561
                                            · linarith only [h2561, hlam, p2528_0]
                                            · rcases p2528_3 (m.d 2 5) (by simp) with h2563 | h2563
                                              · linarith only [h2454, h2563, hlam]
                                              · linarith only [h2470, h2563, hlam]
                                        · linarith only [h2558, hlam, p2528_0]
                                      · linarith only [h2557, h5, hlam]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p2528_1, u5ehi2]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h4, hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h2452, hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h2466, hlam, p2528_1]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h2468, hlam, p2528_1]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h5, hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h2453, hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h2470, hc23, hc45, hlam, hphi, ht34, p2528_1]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h2470, hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h6, hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h2454, hlam, p2528_0]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h0, h2454, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2528_1]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [h0, h2453, h2465, h2470, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2528_1]
                                    · have p2528_0 := h2528c.1
                                      have p2528_1 := h2528c.2.1
                                      have p2528_2 := h2528c.2.2.1
                                      have p2528_3 := h2528c.2.2.2
                                      linarith only [hlam, p2528_0]
                                  · linarith only [h2457, h2527, hlam]
                                · linarith only [h2455, h2526, hlam]
                            · linarith only [h2452, h2523, hlam]
                          · linarith only [h1, h2522, hlam]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [h2465, hlam, p2473_0]
                        · have p2473_0 := h2473c.1
                          have p2473_1 := h2473c.2.1
                          have p2473_2 := h2473c.2.2.1
                          have p2473_3 := h2473c.2.2.2
                          linarith only [hlam, p2473_0]
                      · linarith only [h2, h2465, h2472, h7, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2591 | h2591
                · linarith only [h2451, h2452, h2455, h2465, h2591, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2593 | h2593
                  · linarith only [h2451, h2452, h2455, h2457, h2465, h2593, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2595 | h2595
                    · linarith only [h0, h2453, h2455, h2465, h2595, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2597 | h2597
                      · rcases h1bigk with h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c | h2598c
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h2454, hc01, hlam, hphi, ht0b, ht5b, p2598_1, u5ehi2]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          rcases p2598_3 (m.d 0 1) (by simp) with h2601 | h2601
                          · rcases p2598_3 (m.d 1 2) (by simp) with h2602 | h2602
                            · linarith only [h0, h2602, hlam]
                            · linarith only [h2452, h2602, hlam]
                          · linarith only [h2601, hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          rcases p2598_3 (m.d 0 1) (by simp) with h2606 | h2606
                          · rcases p2598_3 (m.d 1 2) (by simp) with h2607 | h2607
                            · linarith only [h0, h2607, hlam]
                            · linarith only [h2453, h2607, hlam]
                          · linarith only [h2606, hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          rcases p2598_3 (m.d 0 1) (by simp) with h2611 | h2611
                          · rcases p2598_3 (m.d 1 2) (by simp) with h2612 | h2612
                            · linarith only [h0, h2612, hlam]
                            · linarith only [h2454, h2612, hlam]
                          · linarith only [h2611, hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h0, hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          rcases p2598_3 (m.d 0 1) (by simp) with h2618 | h2618
                          · rcases p2598_3 (m.d 1 2) (by simp) with h2619 | h2619
                            · rcases p2598_3 (m.d 1 3) (by simp) with h2620 | h2620
                              · linarith only [h2452, h2620, hlam]
                              · rcases p2598_3 (m.d 1 4) (by simp) with h2622 | h2622
                                · linarith only [h2453, h2622, hlam]
                                · linarith only [h2455, h2622, hlam]
                            · linarith only [h2452, h2619, hlam]
                          · linarith only [h1, h2618, hlam]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          rcases p2598_3 (m.d 0 1) (by simp) with h2627 | h2627
                          · rcases p2598_3 (m.d 1 2) (by simp) with h2628 | h2628
                            · rcases p2598_3 (m.d 1 3) (by simp) with h2629 | h2629
                              · linarith only [h2452, h2629, hlam]
                              · rcases p2598_3 (m.d 1 4) (by simp) with h2631 | h2631
                                · linarith only [h2453, h2631, hlam]
                                · rcases p2598_3 (m.d 1 5) (by simp) with h2633 | h2633
                                  · linarith only [h2454, h2633, hlam]
                                  · linarith only [h2465, h2633, hlam]
                            · linarith only [h2453, h2628, hlam]
                          · linarith only [h2, h2627, hlam]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h0, h2454, hc01, hlam, hphi, ht0b, ht5b, p2598_1, u5ehi2]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h1, hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h2452, hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h2455, hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h2457, hlam, p2598_1]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h2, hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h2453, hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h2451, h2452, h2465, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2598_1]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h2465, hlam, p2598_1]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h3, hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h2454, hlam, p2598_0]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h2451, h2452, h2465, h7, hc23, hc34, hlam, hphi, p2598_1]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [h2451, h2452, h2455, h2465, h7, hc23, hc34, hlam, hphi, p2598_1]
                        · have p2598_0 := h2598c.1
                          have p2598_1 := h2598c.2.1
                          have p2598_2 := h2598c.2.2.1
                          have p2598_3 := h2598c.2.2.2
                          linarith only [hlam, p2598_0]
                      · linarith only [h2451, h2597, h7, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2655 | h2655
          · linarith only [h1, h2451, h2655, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2657 | h2657
            · linarith only [h0, h2453, h2454, h2655, h2657, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2659 | h2659
              · linarith only [h0, h2453, h2454, h2659, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2661 | h2661
                · linarith only [h0, h2452, h2454, h2661, h6, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2663 | h2663
                  · linarith only [h2452, h2454, h2657, h2663, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2665 | h2665
                    · linarith only [h0, h2453, h2655, h2659, h2665, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2451, h2452, h2454, h2665, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2668 | h2668
        · linarith only [h0, h2453, h2668, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2670 | h2670
          · linarith only [h1, h2451, h2452, h2668, h2670, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2672 | h2672
            · linarith only [h0, h2452, h2453, h2672, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2674 | h2674
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2675 | h2675
                · linarith only [h0, h2452, h2453, h2675, h5, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2677 | h2677
                  · linarith only [h2452, h2668, h2672, h2677, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2679 | h2679
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2680 | h2680
                      · rcases h1bigk with h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          rcases p2681_3 (m.d 0 1) (by simp) with h2683 | h2683
                          · rcases p2681_3 (m.d 1 2) (by simp) with h2684 | h2684
                            · linarith only [h2684, hlam, p2681_0]
                            · rcases p2681_3 (m.d 1 3) (by simp) with h2686 | h2686
                              · linarith only [h1, h2686, hlam]
                              · rcases p2681_3 (m.d 1 4) (by simp) with h2688 | h2688
                                · linarith only [h2, h2688, hlam]
                                · linarith only [h2453, h2688, hlam]
                          · linarith only [h2683, hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          rcases p2681_3 (m.d 0 1) (by simp) with h2692 | h2692
                          · rcases p2681_3 (m.d 1 2) (by simp) with h2693 | h2693
                            · linarith only [h0, h2693, hlam]
                            · linarith only [h2452, h2693, hlam]
                          · linarith only [h2692, hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h2674, hc01, hlam, hphi, ht0b, ht5b, p2681_1, u5ehi4]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          rcases p2681_3 (m.d 0 1) (by simp) with h2698 | h2698
                          · rcases p2681_3 (m.d 1 2) (by simp) with h2699 | h2699
                            · linarith only [h0, h2699, hlam]
                            · rcases p2681_3 (m.d 1 3) (by simp) with h2701 | h2701
                              · linarith only [h1, h2701, hlam]
                              · rcases p2681_3 (m.d 1 4) (by simp) with h2703 | h2703
                                · linarith only [h2, h2703, hlam]
                                · linarith only [h2674, h2703, hlam]
                          · linarith only [h2698, hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h0, hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h2668, h2679, h5, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2681_1]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h2453, hlam, p2681_1]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h2668, hlam, p2681_1]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h1, hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h2452, hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h2670, hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h2672, hlam, p2681_1]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h2, hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h2, h2452, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2681_1]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          rcases p2681_3 (m.d 0 1) (by simp) with h2719 | h2719
                          · rcases p2681_3 (m.d 1 2) (by simp) with h2720 | h2720
                            · linarith only [h2453, h2720, hlam]
                            · linarith only [h2452, h2720, hlam]
                          · linarith only [h1, h2719, hlam]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h0, h2452, h2453, h2668, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2681_1]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h3, hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h2452, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2681_1]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          rcases p2681_3 (m.d 0 1) (by simp) with h2728 | h2728
                          · rcases p2681_3 (m.d 1 2) (by simp) with h2729 | h2729
                            · linarith only [h2668, h2729, hlam]
                            · linarith only [h2452, h2729, hlam]
                          · linarith only [h1, h2728, hlam]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [h2674, hlam, p2681_0]
                        · have p2681_0 := h2681c.1
                          have p2681_1 := h2681c.2.1
                          have p2681_2 := h2681c.2.2.1
                          have p2681_3 := h2681c.2.2.2
                          linarith only [hlam, p2681_0]
                      · linarith only [h2451, h2680, h7, hlam]
                    · linarith only [h2453, h2674, h2679, hlam]
              · linarith only [h2451, h2452, h2453, h2674, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2738 | h2738
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2739 | h2739
        · linarith only [h2452, h2739, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2741 | h2741
          · linarith only [h2452, h2741, h4, h7, hlam]
          · linarith only [h2452, h2738, h2741, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2744 | h2744
        · linarith only [h2452, h2744, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2746 | h2746
          · linarith only [h1, h2452, h2746, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2748 | h2748
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2749 | h2749
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2750 | h2750
                · linarith only [h2750, h4, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2752 | h2752
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2753 | h2753
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2754 | h2754
                      · rcases h1bigk with h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          rcases p2755_3 (m.d 0 1) (by simp) with h2757 | h2757
                          · rcases p2755_3 (m.d 1 2) (by simp) with h2758 | h2758
                            · linarith only [h2758, hlam, p2755_0]
                            · rcases p2755_3 (m.d 1 3) (by simp) with h2760 | h2760
                              · linarith only [h1, h2760, hlam]
                              · linarith only [h2452, h2760, hlam]
                          · linarith only [h2757, hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2748, h2754, hc01, hlam, hphi, ht0b, ht5b, p2755_1, u5ehi4]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2746, h2748, h2754, hc01, hlam, hphi, ht0b, ht5b, p2755_1, u5ehi4]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          rcases p2755_3 (m.d 0 1) (by simp) with h2766 | h2766
                          · rcases p2755_3 (m.d 1 2) (by simp) with h2767 | h2767
                            · linarith only [h0, h2767, hlam]
                            · rcases p2755_3 (m.d 1 3) (by simp) with h2769 | h2769
                              · linarith only [h1, h2769, hlam]
                              · linarith only [h2748, h2769, hlam]
                          · linarith only [h2766, hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h0, hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2452, hlam, p2755_1]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2738, hlam, p2755_1]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2744, hlam, p2755_1]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h1, hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2452, h4, h7, hc12, hc34, hlam, hphi, ht23, p2755_1]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2746, hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2452, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2755_1, u5ehi1]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2, hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          rcases p2755_3 (m.d 0 1) (by simp) with h2784 | h2784
                          · rcases p2755_3 (m.d 1 2) (by simp) with h2785 | h2785
                            · linarith only [h2738, h2785, hlam]
                            · rcases p2755_3 (m.d 1 3) (by simp) with h2787 | h2787
                              · linarith only [h2746, h2787, hlam]
                              · linarith only [h2452, h2787, hlam]
                          · linarith only [h0, h2784, hlam]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h0, h2738, h2748, h5, hc01, hlam, hphi, ht0b, ht5b, p2755_1, u5ehi3]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h0, h2738, h2748, h2754, h5, hc01, hlam, hphi, ht0b, ht5b, p2755_1, u5ehi4]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h3, hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2744, h2752, h4, h7, hc12, hc34, hlam, hphi, ht23, p2755_1]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2748, hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [h2749, hlam, p2755_0]
                        · have p2755_0 := h2755c.1
                          have p2755_1 := h2755c.2.1
                          have p2755_2 := h2755c.2.2.1
                          have p2755_3 := h2755c.2.2.2
                          linarith only [hlam, p2755_0]
                      · linarith only [h2452, h2748, h2754, h4, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                    · linarith only [h2738, h2749, h2753, hlam]
                  · linarith only [h2452, h2748, h2752, hlam]
              · linarith only [h2451, h2746, h2748, h2749, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2803 | h2803
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2804 | h2804
                · linarith only [h0, h2, h2803, h2804, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2806 | h2806
                  · linarith only [h2748, h2806, h4, h7, hc13, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2808 | h2808
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2809 | h2809
                      · rcases h1bigk with h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          rcases p2810_3 (m.d 0 1) (by simp) with h2812 | h2812
                          · rcases p2810_3 (m.d 1 2) (by simp) with h2813 | h2813
                            · linarith only [h2813, hlam, p2810_0]
                            · rcases p2810_3 (m.d 1 3) (by simp) with h2815 | h2815
                              · linarith only [h1, h2815, hlam]
                              · linarith only [h2452, h2815, hlam]
                          · linarith only [h2812, hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          rcases p2810_3 (m.d 0 1) (by simp) with h2819 | h2819
                          · rcases p2810_3 (m.d 1 2) (by simp) with h2820 | h2820
                            · linarith only [h0, h2820, hlam]
                            · rcases p2810_3 (m.d 1 3) (by simp) with h2822 | h2822
                              · linarith only [h2822, hlam, p2810_0]
                              · rcases p2810_3 (m.d 1 4) (by simp) with h2824 | h2824
                                · linarith only [h2, h2824, hlam]
                                · linarith only [h2746, h2824, hlam]
                          · linarith only [h2819, hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h2803, hc01, hlam, hphi, ht0b, ht5b, p2810_1, u5ehi4]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          rcases p2810_3 (m.d 0 1) (by simp) with h2829 | h2829
                          · rcases p2810_3 (m.d 1 2) (by simp) with h2830 | h2830
                            · linarith only [h0, h2830, hlam]
                            · rcases p2810_3 (m.d 1 3) (by simp) with h2832 | h2832
                              · linarith only [h1, h2832, hlam]
                              · rcases p2810_3 (m.d 1 4) (by simp) with h2834 | h2834
                                · linarith only [h2, h2834, hlam]
                                · linarith only [h2803, h2834, hlam]
                          · linarith only [h2829, hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h0, hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h2452, hlam, p2810_1]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h2738, hlam, p2810_1]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h2744, hlam, p2810_1]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h1, hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h1, h7, hc12, hc34, hlam, hphi, ht23, p2810_1]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h2746, hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h2748, hlam, p2810_1]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h2, hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          rcases p2810_3 (m.d 0 1) (by simp) with h2849 | h2849
                          · rcases p2810_3 (m.d 1 2) (by simp) with h2850 | h2850
                            · linarith only [h2738, h2850, hlam]
                            · rcases p2810_3 (m.d 1 3) (by simp) with h2852 | h2852
                              · linarith only [h2746, h2852, hlam]
                              · linarith only [h2452, h2852, hlam]
                          · linarith only [h0, h2849, hlam]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          rcases p2810_3 (m.d 0 1) (by simp) with h2856 | h2856
                          · rcases p2810_3 (m.d 1 2) (by simp) with h2857 | h2857
                            · linarith only [h2738, h2857, hlam]
                            · rcases p2810_3 (m.d 1 3) (by simp) with h2859 | h2859
                              · linarith only [h2746, h2859, hlam]
                              · rcases p2810_3 (m.d 1 4) (by simp) with h2861 | h2861
                                · rcases p2810_3 (m.d 1 5) (by simp) with h2862 | h2862
                                  · linarith only [h2803, h2862, hlam]
                                  · linarith only [h2748, h2862, hlam]
                                · linarith only [h2746, h2861, hlam]
                          · linarith only [h1, h2856, hlam]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p2810_1, u5ehi1]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h3, hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          rcases p2810_3 (m.d 0 1) (by simp) with h2870 | h2870
                          · rcases p2810_3 (m.d 1 2) (by simp) with h2871 | h2871
                            · linarith only [h2744, h2871, hlam]
                            · rcases p2810_3 (m.d 1 3) (by simp) with h2873 | h2873
                              · linarith only [h2748, h2873, hlam]
                              · linarith only [h2452, h2873, hlam]
                          · linarith only [h0, h2870, hlam]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          rcases p2810_3 (m.d 0 1) (by simp) with h2877 | h2877
                          · rcases p2810_3 (m.d 1 2) (by simp) with h2878 | h2878
                            · linarith only [h2744, h2878, hlam]
                            · rcases p2810_3 (m.d 1 3) (by simp) with h2880 | h2880
                              · linarith only [h2748, h2880, hlam]
                              · rcases p2810_3 (m.d 1 4) (by simp) with h2882 | h2882
                                · rcases p2810_3 (m.d 1 5) (by simp) with h2883 | h2883
                                  · rcases h2bigk with h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2452, h2738, h2803, h5, hlam, p2810_1, p2884_2]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      rcases p2884_3 (m.d 0 2) (by simp) with h2887 | h2887
                                      · rcases p2884_3 (m.d 1 2) (by simp) with h2888 | h2888
                                        · linarith only [h0, h2888, hlam]
                                        · rcases p2884_3 (m.d 2 3) (by simp) with h2890 | h2890
                                          · linarith only [h2890, hlam, p2884_0]
                                          · rcases p2884_3 (m.d 2 4) (by simp) with h2892 | h2892
                                            · linarith only [h2892, h5, hlam]
                                            · linarith only [h2804, h2892, hlam]
                                      · linarith only [h2887, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h0, h2452, h2738, h2803, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2810_1, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h0, h2452, h2744, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2810_1, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h0, hlam, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2452, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2738, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2744, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h4, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2804, hlam, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2806, hlam, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h5, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      rcases p2884_3 (m.d 0 2) (by simp) with h2909 | h2909
                                      · rcases p2884_3 (m.d 1 2) (by simp) with h2910 | h2910
                                        · linarith only [h2910, hlam, p2884_0]
                                        · rcases p2884_3 (m.d 2 3) (by simp) with h2912 | h2912
                                          · linarith only [h2804, h2912, hlam]
                                          · linarith only [h2452, h2912, hlam]
                                      · linarith only [h0, h2909, hlam]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2452, hc12, hc24, hlam, hphi, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h0, h2452, h2744, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2810_1, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h6, hlam, p2884_0]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      rcases p2884_3 (m.d 0 2) (by simp) with h2920 | h2920
                                      · rcases p2884_3 (m.d 1 2) (by simp) with h2921 | h2921
                                        · linarith only [h2921, hlam, p2884_0]
                                        · rcases p2884_3 (m.d 2 3) (by simp) with h2923 | h2923
                                          · linarith only [h2806, h2923, hlam]
                                          · linarith only [h2452, h2923, hlam]
                                      · linarith only [h0, h2920, hlam]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2452, hc12, hc25, hlam, hphi, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [h2808, hlam, p2884_1]
                                    · have p2884_0 := h2884c.1
                                      have p2884_1 := h2884c.2.1
                                      have p2884_2 := h2884c.2.2.1
                                      have p2884_3 := h2884c.2.2.2
                                      linarith only [hlam, p2884_0]
                                  · linarith only [h2748, h2883, hlam]
                                · linarith only [h2746, h2882, hlam]
                          · linarith only [h1, h2877, hlam]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [h2803, hlam, p2810_0]
                        · have p2810_0 := h2810c.1
                          have p2810_1 := h2810c.2.1
                          have p2810_2 := h2810c.2.2.1
                          have p2810_3 := h2810c.2.2.2
                          linarith only [hlam, p2810_0]
                      · linarith only [h1, h2, h2452, h2803, h2809, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h2738, h2803, h2808, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2937 | h2937
                · linarith only [h0, h2451, h2803, h2937, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2939 | h2939
                  · linarith only [h2452, h2748, h2939, h4, h7, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2941 | h2941
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2942 | h2942
                      · rcases h1bigk with h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c | h2943c
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [hlam, p2943_0]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h0, h2452, h2746, h2803, h2941, h5, hlam, p2943_2]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h0, h2746, h2803, h2941, h5, hlam, p2943_2]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h0, h2803, h2941, h5, hlam, p2943_2]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          rcases p2943_3 (m.d 0 1) (by simp) with h2948 | h2948
                          · rcases p2943_3 (m.d 1 2) (by simp) with h2949 | h2949
                            · linarith only [h0, h2949, hlam]
                            · rcases p2943_3 (m.d 1 3) (by simp) with h2951 | h2951
                              · linarith only [h1, h2951, hlam]
                              · rcases p2943_3 (m.d 1 4) (by simp) with h2953 | h2953
                                · linarith only [h2, h2953, hlam]
                                · rcases p2943_3 (m.d 1 5) (by simp) with h2955 | h2955
                                  · linarith only [h2955, hlam, p2943_0]
                                  · rcases h2bigk with h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c | h2957c
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h2452, h2746, h2803, h2941, h5, hlam, p2957_2]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      rcases p2957_3 (m.d 0 2) (by simp) with h2960 | h2960
                                      · rcases p2957_3 (m.d 1 2) (by simp) with h2961 | h2961
                                        · linarith only [h0, h2961, hlam]
                                        · rcases p2957_3 (m.d 2 3) (by simp) with h2963 | h2963
                                          · linarith only [h2963, hlam, p2957_0]
                                          · rcases p2957_3 (m.d 2 4) (by simp) with h2965 | h2965
                                            · linarith only [h2965, h5, hlam]
                                            · linarith only [h2937, h2965, hlam]
                                      · linarith only [h2960, hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h0, h2452, h2746, h2803, h2941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2957_1]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      rcases p2957_3 (m.d 0 2) (by simp) with h2970 | h2970
                                      · rcases p2957_3 (m.d 1 2) (by simp) with h2971 | h2971
                                        · linarith only [h0, h2971, hlam]
                                        · rcases p2957_3 (m.d 2 3) (by simp) with h2973 | h2973
                                          · linarith only [h2973, h4, hlam]
                                          · rcases p2957_3 (m.d 2 4) (by simp) with h2975 | h2975
                                            · linarith only [h2975, h5, hlam]
                                            · linarith only [h2941, h2975, hlam]
                                      · linarith only [h2970, hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h0, hlam, p2957_1]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h2452, hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h2738, hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h2744, hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h4, hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h2939, hc12, hc35, hlam, hphi, ht23, p2957_1]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h2937, hlam, p2957_1]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h2939, hlam, p2957_1]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h5, hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      rcases p2957_3 (m.d 0 2) (by simp) with h2990 | h2990
                                      · rcases p2957_3 (m.d 1 2) (by simp) with h2991 | h2991
                                        · linarith only [h2991, hlam, p2957_0]
                                        · rcases p2957_3 (m.d 2 3) (by simp) with h2993 | h2993
                                          · linarith only [h2937, h2993, hlam]
                                          · linarith only [h2452, h2993, hlam]
                                      · linarith only [h0, h2990, hlam]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h2452, hc12, hc24, hlam, hphi, p2957_1]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h0, h2452, h2939, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2957_1]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h6, hlam, p2957_0]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      rcases p2957_3 (m.d 0 2) (by simp) with h3001 | h3001
                                      · rcases p2957_3 (m.d 1 2) (by simp) with h3002 | h3002
                                        · linarith only [h3002, hlam, p2957_0]
                                        · rcases p2957_3 (m.d 2 3) (by simp) with h3004 | h3004
                                          · linarith only [h2939, h3004, hlam]
                                          · linarith only [h2452, h3004, hlam]
                                      · linarith only [h0, h3001, hlam]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h2452, hc12, hc25, hlam, hphi, p2957_1]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [h2941, hlam, p2957_1]
                                    · have p2957_0 := h2957c.1
                                      have p2957_1 := h2957c.2.1
                                      have p2957_2 := h2957c.2.2.1
                                      have p2957_3 := h2957c.2.2.2
                                      linarith only [hlam, p2957_0]
                          · linarith only [h2948, hlam, p2943_0]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h0, hlam, p2943_0]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [hlam, p2943_0]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2452, hlam, p2943_1]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2738, hlam, p2943_1]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2744, hlam, p2943_1]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h1, hlam, p2943_0]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2746, h2803, hc12, hc45, hlam, hphi, ht23, ht34, p2943_1]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [hlam, p2943_0]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2746, hlam, p2943_0]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2748, hlam, p2943_1]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2, hlam, p2943_0]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2451, h2803, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2943_1]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2451, h2803, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2943_1]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [hlam, p2943_0]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2803, hlam, p2943_1]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h3, hlam, p2943_0]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2451, h2803, h7, hc12, hc34, hlam, hphi, ht23, p2943_1]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2451, h2452, h2803, h7, hc12, hc34, hlam, hphi, ht23, p2943_1]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [h2451, h2738, h2803, h7, hc12, hc34, hlam, hphi, ht23, p2943_1]
                        · have p2943_0 := h2943c.1
                          have p2943_1 := h2943c.2.1
                          have p2943_2 := h2943c.2.2.1
                          have p2943_3 := h2943c.2.2.2
                          linarith only [hlam, p2943_0]
                      · linarith only [h0, h2941, h2942, h5, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2451, h2738, h2941, h7, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3034 | h3034
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3035 | h3035
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3036 | h3036
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3037 | h3037
          · linarith only [h1, h3037, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3039 | h3039
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3040 | h3040
              · linarith only [h0, h1, h2451, h3035, h3039, h3040, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h3037, h3039, h3040, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3043 | h3043
              · linarith only [h2, h2451, h3043, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3045 | h3045
                · linarith only [h1, h3034, h3045, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3047 | h3047
                  · linarith only [h3034, h3039, h3047, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3049 | h3049
                    · linarith only [h2451, h3049, h5, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3051 | h3051
                      · rcases h1bigk with h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c | h3052c
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h3036, hc01, hlam, hphi, ht0b, ht5b, p3052_1, u5ehi2]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          rcases p3052_3 (m.d 0 1) (by simp) with h3055 | h3055
                          · rcases p3052_3 (m.d 1 2) (by simp) with h3056 | h3056
                            · linarith only [h0, h3056, hlam]
                            · linarith only [h3034, h3056, hlam]
                          · linarith only [h3055, hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          rcases p3052_3 (m.d 0 1) (by simp) with h3060 | h3060
                          · rcases p3052_3 (m.d 1 2) (by simp) with h3061 | h3061
                            · linarith only [h0, h3061, hlam]
                            · linarith only [h3035, h3061, hlam]
                          · linarith only [h3060, hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          rcases p3052_3 (m.d 0 1) (by simp) with h3065 | h3065
                          · rcases p3052_3 (m.d 1 2) (by simp) with h3066 | h3066
                            · linarith only [h0, h3066, hlam]
                            · linarith only [h3036, h3066, hlam]
                          · linarith only [h3065, hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h0, hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          rcases p3052_3 (m.d 0 1) (by simp) with h3072 | h3072
                          · rcases p3052_3 (m.d 1 2) (by simp) with h3073 | h3073
                            · rcases p3052_3 (m.d 1 3) (by simp) with h3074 | h3074
                              · linarith only [h3034, h3074, hlam]
                              · rcases p3052_3 (m.d 1 4) (by simp) with h3076 | h3076
                                · linarith only [h3035, h3076, hlam]
                                · linarith only [h3037, h3076, hlam]
                            · linarith only [h3034, h3073, hlam]
                          · linarith only [h1, h3072, hlam]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          rcases p3052_3 (m.d 0 1) (by simp) with h3081 | h3081
                          · rcases p3052_3 (m.d 1 2) (by simp) with h3082 | h3082
                            · rcases p3052_3 (m.d 1 3) (by simp) with h3083 | h3083
                              · linarith only [h3034, h3083, hlam]
                              · rcases p3052_3 (m.d 1 4) (by simp) with h3085 | h3085
                                · linarith only [h3035, h3085, hlam]
                                · rcases p3052_3 (m.d 1 5) (by simp) with h3087 | h3087
                                  · linarith only [h3036, h3087, hlam]
                                  · linarith only [h3043, h3087, hlam]
                            · linarith only [h3035, h3082, hlam]
                          · linarith only [h2, h3081, hlam]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h0, h3036, hc01, hlam, hphi, ht0b, ht5b, p3052_1, u5ehi2]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h1, hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h3034, hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h3037, hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h3039, hlam, p3052_1]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h2, hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h3035, hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h2, h2451, h3034, h3051, hc23, hc34, hlam, hphi, p3052_1]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h3043, hlam, p3052_1]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h3, hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h3036, hlam, p3052_0]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h2451, h3, h3034, h3051, hc23, hc34, hlam, hphi, p3052_1]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [h2451, h3, h3034, h3037, h3051, hc23, hc34, hlam, hphi, p3052_1]
                        · have p3052_0 := h3052c.1
                          have p3052_1 := h3052c.2.1
                          have p3052_2 := h3052c.2.2.1
                          have p3052_3 := h3052c.2.2.2
                          linarith only [hlam, p3052_0]
                      · rcases h1bigk with h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c | h3108c
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h3036, hc01, hlam, hphi, ht0b, ht5b, p3108_1, u5ehi2]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          rcases p3108_3 (m.d 0 1) (by simp) with h3111 | h3111
                          · rcases p3108_3 (m.d 1 2) (by simp) with h3112 | h3112
                            · linarith only [h0, h3112, hlam]
                            · linarith only [h3034, h3112, hlam]
                          · linarith only [h3111, hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          rcases p3108_3 (m.d 0 1) (by simp) with h3116 | h3116
                          · rcases p3108_3 (m.d 1 2) (by simp) with h3117 | h3117
                            · linarith only [h0, h3117, hlam]
                            · linarith only [h3035, h3117, hlam]
                          · linarith only [h3116, hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          rcases p3108_3 (m.d 0 1) (by simp) with h3121 | h3121
                          · rcases p3108_3 (m.d 1 2) (by simp) with h3122 | h3122
                            · linarith only [h0, h3122, hlam]
                            · linarith only [h3036, h3122, hlam]
                          · linarith only [h3121, hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h0, hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          rcases p3108_3 (m.d 0 1) (by simp) with h3128 | h3128
                          · rcases p3108_3 (m.d 1 2) (by simp) with h3129 | h3129
                            · rcases p3108_3 (m.d 1 3) (by simp) with h3130 | h3130
                              · linarith only [h3034, h3130, hlam]
                              · rcases p3108_3 (m.d 1 4) (by simp) with h3132 | h3132
                                · linarith only [h3035, h3132, hlam]
                                · linarith only [h3037, h3132, hlam]
                            · linarith only [h3034, h3129, hlam]
                          · linarith only [h1, h3128, hlam]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          rcases p3108_3 (m.d 0 1) (by simp) with h3137 | h3137
                          · rcases p3108_3 (m.d 1 2) (by simp) with h3138 | h3138
                            · rcases p3108_3 (m.d 1 3) (by simp) with h3139 | h3139
                              · linarith only [h3034, h3139, hlam]
                              · rcases p3108_3 (m.d 1 4) (by simp) with h3141 | h3141
                                · linarith only [h3035, h3141, hlam]
                                · rcases p3108_3 (m.d 1 5) (by simp) with h3143 | h3143
                                  · linarith only [h3036, h3143, hlam]
                                  · linarith only [h3043, h3143, hlam]
                            · linarith only [h3035, h3138, hlam]
                          · linarith only [h2, h3137, hlam]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p3108_1, u5ehi1]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h1, hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h3034, hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h3037, hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h3039, hlam, p3108_1]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h2, hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h3035, hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h2, h3034, h3051, h7, hc23, hc45, hlam, hphi, ht34, p3108_1]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h3043, hlam, p3108_1]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h3, hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [h3036, hlam, p3108_0]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          rcases p3108_3 (m.d 0 1) (by simp) with h3161 | h3161
                          · rcases p3108_3 (m.d 1 2) (by simp) with h3162 | h3162
                            · rcases p3108_3 (m.d 1 3) (by simp) with h3163 | h3163
                              · linarith only [h3039, h3163, hlam]
                              · rcases p3108_3 (m.d 1 4) (by simp) with h3165 | h3165
                                · linarith only [h3043, h3165, hlam]
                                · linarith only [h3037, h3165, hlam]
                            · linarith only [h3034, h3162, hlam]
                          · linarith only [h1, h3161, hlam]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          rcases p3108_3 (m.d 0 1) (by simp) with h3170 | h3170
                          · rcases p3108_3 (m.d 1 2) (by simp) with h3171 | h3171
                            · rcases p3108_3 (m.d 1 3) (by simp) with h3172 | h3172
                              · linarith only [h3039, h3172, hlam]
                              · rcases p3108_3 (m.d 1 4) (by simp) with h3174 | h3174
                                · linarith only [h3043, h3174, hlam]
                                · rcases p3108_3 (m.d 1 5) (by simp) with h3176 | h3176
                                  · rcases h2bigk with h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h3034, h3036, h3037, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3108_1, p3177_1]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      rcases p3177_3 (m.d 0 2) (by simp) with h3180 | h3180
                                      · rcases p3177_3 (m.d 1 2) (by simp) with h3181 | h3181
                                        · linarith only [h0, h3181, hlam]
                                        · linarith only [h3034, h3181, hlam]
                                      · linarith only [h3180, hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      rcases p3177_3 (m.d 0 2) (by simp) with h3185 | h3185
                                      · rcases p3177_3 (m.d 1 2) (by simp) with h3186 | h3186
                                        · linarith only [h0, h3186, hlam]
                                        · linarith only [h3035, h3186, hlam]
                                      · linarith only [h3185, hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      rcases p3177_3 (m.d 0 2) (by simp) with h3190 | h3190
                                      · rcases p3177_3 (m.d 1 2) (by simp) with h3191 | h3191
                                        · linarith only [h0, h3191, hlam]
                                        · linarith only [h3036, h3191, hlam]
                                      · linarith only [h3190, hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h0, hlam, p3177_1]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      rcases p3177_3 (m.d 0 2) (by simp) with h3197 | h3197
                                      · rcases p3177_3 (m.d 1 2) (by simp) with h3198 | h3198
                                        · rcases p3177_3 (m.d 2 3) (by simp) with h3199 | h3199
                                          · linarith only [h3199, hlam, p3177_0]
                                          · rcases p3177_3 (m.d 2 4) (by simp) with h3201 | h3201
                                            · linarith only [h3035, h3201, hlam]
                                            · linarith only [h3045, h3201, hlam]
                                        · linarith only [h3198, hlam, p3177_0]
                                      · linarith only [h3197, h4, hlam]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      rcases p3177_3 (m.d 0 2) (by simp) with h3206 | h3206
                                      · rcases p3177_3 (m.d 1 2) (by simp) with h3207 | h3207
                                        · rcases p3177_3 (m.d 2 3) (by simp) with h3208 | h3208
                                          · linarith only [h3034, h3208, hlam]
                                          · rcases p3177_3 (m.d 2 4) (by simp) with h3210 | h3210
                                            · linarith only [h3210, hlam, p3177_0]
                                            · rcases p3177_3 (m.d 2 5) (by simp) with h3212 | h3212
                                              · linarith only [h3036, h3212, hlam]
                                              · linarith only [h3049, h3212, hlam]
                                        · linarith only [h3207, hlam, p3177_0]
                                      · linarith only [h3206, h5, hlam]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p3177_1, u5ehi2]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h4, hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h3034, hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h3045, hlam, p3177_1]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h3047, hlam, p3177_1]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h5, hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h3035, hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h3, h3035, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3108_1, p3177_1]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h3049, hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h6, hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h3036, hlam, p3177_0]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h0, h3036, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3177_1]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [h0, h3036, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3177_1]
                                    · have p3177_0 := h3177c.1
                                      have p3177_1 := h3177c.2.1
                                      have p3177_2 := h3177c.2.2.1
                                      have p3177_3 := h3177c.2.2.2
                                      linarith only [hlam, p3177_0]
                                  · linarith only [h3043, h3176, hlam]
                            · linarith only [h3035, h3171, hlam]
                          · linarith only [h2, h3170, hlam]
                        · have p3108_0 := h3108c.1
                          have p3108_1 := h3108c.2.1
                          have p3108_2 := h3108c.2.2.1
                          have p3108_3 := h3108c.2.2.2
                          linarith only [hlam, p3108_0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3237 | h3237
          · linarith only [h1, h3237, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3239 | h3239
            · linarith only [h0, h3034, h3036, h3239, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3241 | h3241
              · linarith only [h0, h2451, h3035, h3036, h3241, h6, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3243 | h3243
                · linarith only [h1, h3034, h3243, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3245 | h3245
                  · linarith only [h0, h3034, h3036, h3239, h3245, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3247 | h3247
                    · linarith only [h0, h2451, h3035, h3036, h3247, h6, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3249 | h3249
                      · linarith only [h2451, h3034, h3036, h3249, h6, hc23, hc34, hlam, hphi]
                      · rcases h1bigk with h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          rcases p3251_3 (m.d 0 1) (by simp) with h3253 | h3253
                          · rcases p3251_3 (m.d 1 2) (by simp) with h3254 | h3254
                            · linarith only [h3254, hlam, p3251_0]
                            · rcases p3251_3 (m.d 1 3) (by simp) with h3256 | h3256
                              · linarith only [h1, h3256, hlam]
                              · rcases p3251_3 (m.d 1 4) (by simp) with h3258 | h3258
                                · linarith only [h2, h3258, hlam]
                                · rcases p3251_3 (m.d 1 5) (by simp) with h3260 | h3260
                                  · linarith only [h3, h3260, hlam]
                                  · linarith only [h3036, h3260, hlam]
                          · linarith only [h3253, hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          rcases p3251_3 (m.d 0 1) (by simp) with h3264 | h3264
                          · rcases p3251_3 (m.d 1 2) (by simp) with h3265 | h3265
                            · linarith only [h0, h3265, hlam]
                            · linarith only [h3034, h3265, hlam]
                          · linarith only [h3264, hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          rcases p3251_3 (m.d 0 1) (by simp) with h3269 | h3269
                          · rcases p3251_3 (m.d 1 2) (by simp) with h3270 | h3270
                            · linarith only [h0, h3270, hlam]
                            · linarith only [h3035, h3270, hlam]
                          · linarith only [h3269, hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          rcases p3251_3 (m.d 0 1) (by simp) with h3274 | h3274
                          · rcases p3251_3 (m.d 1 2) (by simp) with h3275 | h3275
                            · linarith only [h0, h3275, hlam]
                            · rcases p3251_3 (m.d 1 3) (by simp) with h3277 | h3277
                              · linarith only [h1, h3277, hlam]
                              · rcases p3251_3 (m.d 1 4) (by simp) with h3279 | h3279
                                · linarith only [h2, h3279, hlam]
                                · rcases p3251_3 (m.d 1 5) (by simp) with h3281 | h3281
                                  · linarith only [h3281, hlam, p3251_0]
                                  · rcases h2bigk with h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [hlam, p3283_0]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      rcases p3283_3 (m.d 0 2) (by simp) with h3285 | h3285
                                      · rcases p3283_3 (m.d 1 2) (by simp) with h3286 | h3286
                                        · linarith only [h0, h3286, hlam]
                                        · rcases p3283_3 (m.d 2 3) (by simp) with h3288 | h3288
                                          · linarith only [h3288, h4, hlam]
                                          · rcases p3283_3 (m.d 2 4) (by simp) with h3290 | h3290
                                            · linarith only [h3290, h5, hlam]
                                            · rcases p3283_3 (m.d 2 5) (by simp) with h3292 | h3292
                                              · linarith only [h3292, h6, hlam]
                                              · linarith only [h3036, h3292, hlam]
                                      · linarith only [h0, h3285, hlam]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h3035, h3036, h3243, h6, hlam, p3283_2]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h3035, h3036, h6, hlam, p3283_2]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h0, h3035, h3036, h3243, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3283_1]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h0, hlam, p3283_1]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [hlam, p3283_0]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h3036, h3245, hc23, hc35, hlam, hphi, p3283_1]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h3036, h3243, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3251_1, p3283_1]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h3036, hlam, p3283_0]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h4, hlam, p3283_0]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h3034, hlam, p3283_0]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [hlam, p3283_0]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h3243, hlam, p3283_1]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h3245, hlam, p3283_1]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h5, hlam, p3283_0]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h3035, hlam, p3283_0]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h3249, h5, h7, hc23, hc45, hlam, hphi, ht34, p3283_1]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [hlam, p3283_0]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h3247, hlam, p3283_0]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h6, hlam, p3283_0]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [h0, h3035, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3283_1]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      rcases p3283_3 (m.d 0 2) (by simp) with h3316 | h3316
                                      · rcases p3283_3 (m.d 1 2) (by simp) with h3317 | h3317
                                        · linarith only [h3036, h3317, hlam]
                                        · linarith only [h3034, h3317, hlam]
                                      · linarith only [h3316, h4, hlam]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      rcases p3283_3 (m.d 0 2) (by simp) with h3321 | h3321
                                      · rcases p3283_3 (m.d 1 2) (by simp) with h3322 | h3322
                                        · linarith only [h3036, h3322, hlam]
                                        · linarith only [h3035, h3322, hlam]
                                      · linarith only [h3321, h5, hlam]
                                    · have p3283_0 := h3283c.1
                                      have p3283_1 := h3283c.2.1
                                      have p3283_2 := h3283c.2.2.1
                                      have p3283_3 := h3283c.2.2.2
                                      linarith only [hlam, p3283_0]
                          · linarith only [h3274, hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h0, hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h0, h3034, h3036, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3251_1]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h0, h3036, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3251_1]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h3036, hlam, p3251_1]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h1, hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h3034, hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h3237, hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h3239, hlam, p3251_1]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h2, hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h3035, hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h2, h3034, h3249, h7, hc23, hc45, hlam, hphi, ht34, p3251_1]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h3241, hlam, p3251_1]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h3, hlam, p3251_0]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [h3, h3034, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3251_1]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          rcases p3251_3 (m.d 0 1) (by simp) with h3345 | h3345
                          · rcases p3251_3 (m.d 1 2) (by simp) with h3346 | h3346
                            · linarith only [h3036, h3346, hlam]
                            · linarith only [h3034, h3346, hlam]
                          · linarith only [h1, h3345, hlam]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          rcases p3251_3 (m.d 0 1) (by simp) with h3350 | h3350
                          · rcases p3251_3 (m.d 1 2) (by simp) with h3351 | h3351
                            · linarith only [h3036, h3351, hlam]
                            · linarith only [h3035, h3351, hlam]
                          · linarith only [h2, h3350, hlam]
                        · have p3251_0 := h3251c.1
                          have p3251_1 := h3251c.2.1
                          have p3251_2 := h3251c.2.2.1
                          have p3251_3 := h3251c.2.2.2
                          linarith only [hlam, p3251_0]
      · linarith only [h2451, h3034, h3035, h5, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3357 | h3357
      · linarith only [h2451, h3034, h3357, h4, h7, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3359 | h3359
        · linarith only [h2451, h3034, h3359, h4, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3361 | h3361
          · linarith only [h1, h3034, h3361, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3363 | h3363
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3364 | h3364
              · linarith only [h2451, h3034, h3363, h3364, h4, h7, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · linarith only [h3361, h3363, h3364, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3367 | h3367
              · linarith only [h2, h2451, h3034, h3367, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3369 | h3369
                · linarith only [h3369, h4, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3371 | h3371
                  · linarith only [h3034, h3363, h3371, h4, h7, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3373 | h3373
                    · linarith only [h2451, h3373, h5, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3375 | h3375
                      · linarith only [h2451, h3034, h3375, h4, h7, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h3034, h3375, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
