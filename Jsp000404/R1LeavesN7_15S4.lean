import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h1953 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h2134 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h2503 | h2503
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2504 | h2504
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2505 | h2505
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2506 | h2506
        · linarith only [h1, h2506, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2508 | h2508
          · linarith only [h1, h1953, h2508, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2510 | h2510
            · linarith only [h2, h2134, h2510, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2512 | h2512
              · linarith only [h1, h2503, h2512, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2514 | h2514
                · linarith only [h1, h1953, h2503, h2514, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2516 | h2516
                  · linarith only [h2134, h2516, h5, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2518 | h2518
                    · rcases h0bigk with h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c | h2519c
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [hlam, p2519_0]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h0, h2505, h2512, h2516, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        rcases p2519_3 (m.d 0 1) (by simp) with h2522 | h2522
                        · rcases p2519_3 (m.d 0 2) (by simp) with h2523 | h2523
                          · linarith only [h0, h2523, hlam]
                          · linarith only [h2523, h4, hlam]
                        · linarith only [h1, h2522, hlam]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        rcases p2519_3 (m.d 0 1) (by simp) with h2527 | h2527
                        · rcases p2519_3 (m.d 0 2) (by simp) with h2528 | h2528
                          · linarith only [h0, h2528, hlam]
                          · linarith only [h2528, h5, hlam]
                        · linarith only [h2, h2527, hlam]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        rcases p2519_3 (m.d 0 1) (by simp) with h2532 | h2532
                        · rcases p2519_3 (m.d 0 2) (by simp) with h2533 | h2533
                          · linarith only [h0, h2533, hlam]
                          · linarith only [h2533, h6, hlam]
                        · linarith only [h2532, h3, hlam]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h0, hlam, p2519_0]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [hlam, p2519_0]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        rcases p2519_3 (m.d 0 1) (by simp) with h2539 | h2539
                        · rcases p2519_3 (m.d 0 2) (by simp) with h2540 | h2540
                          · rcases p2519_3 (m.d 0 3) (by simp) with h2541 | h2541
                            · linarith only [h2541, h4, hlam]
                            · rcases p2519_3 (m.d 0 4) (by simp) with h2543 | h2543
                              · linarith only [h2543, h5, hlam]
                              · linarith only [h2543, h7, hlam]
                          · linarith only [h2540, h4, hlam]
                        · linarith only [h1, h2539, hlam]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        rcases p2519_3 (m.d 0 1) (by simp) with h2548 | h2548
                        · rcases p2519_3 (m.d 0 2) (by simp) with h2549 | h2549
                          · rcases p2519_3 (m.d 0 3) (by simp) with h2550 | h2550
                            · linarith only [h2550, h4, hlam]
                            · rcases p2519_3 (m.d 0 4) (by simp) with h2552 | h2552
                              · linarith only [h2552, h5, hlam]
                              · rcases p2519_3 (m.d 0 5) (by simp) with h2554 | h2554
                                · linarith only [h2554, h6, hlam]
                                · linarith only [h2134, h2554, hlam]
                          · linarith only [h2549, h5, hlam]
                        · linarith only [h2, h2548, hlam]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        rcases p2519_3 (m.d 0 1) (by simp) with h2559 | h2559
                        · rcases p2519_3 (m.d 0 2) (by simp) with h2560 | h2560
                          · rcases p2519_3 (m.d 0 3) (by simp) with h2561 | h2561
                            · linarith only [h2561, h4, hlam]
                            · rcases p2519_3 (m.d 0 4) (by simp) with h2563 | h2563
                              · linarith only [h2563, h5, hlam]
                              · rcases p2519_3 (m.d 0 5) (by simp) with h2565 | h2565
                                · linarith only [h2565, h6, hlam]
                                · rcases h1bigk with h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [hlam, p2567_0]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    rcases p2567_3 (m.d 0 1) (by simp) with h2569 | h2569
                                    · rcases p2567_3 (m.d 1 2) (by simp) with h2570 | h2570
                                      · linarith only [h2570, hlam, p2567_0]
                                      · rcases p2567_3 (m.d 1 3) (by simp) with h2572 | h2572
                                        · linarith only [h1, h2572, hlam]
                                        · rcases p2567_3 (m.d 1 4) (by simp) with h2574 | h2574
                                          · linarith only [h2, h2574, hlam]
                                          · rcases p2567_3 (m.d 1 5) (by simp) with h2576 | h2576
                                            · linarith only [h2576, h3, hlam]
                                            · rcases h3bigk with h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c | h2578c
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h2134, h2503, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2578_1]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h0, h2134, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2578_1]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h7, hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h1953, hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h1, hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h0, h1, h2134, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2578_1]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h2506, hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h2508, hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h4, hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h2503, hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h2512, hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h2514, hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                rcases p2578_3 (m.d 0 3) (by simp) with h2594 | h2594
                                                · linarith only [h2594, hlam, p2578_0]
                                                · rcases p2578_3 (m.d 1 3) (by simp) with h2596 | h2596
                                                  · linarith only [h2506, h2596, hlam]
                                                  · rcases p2578_3 (m.d 2 3) (by simp) with h2598 | h2598
                                                    · linarith only [h2512, h2598, hlam]
                                                    · rcases p2578_3 (m.d 3 4) (by simp) with h2600 | h2600
                                                      · rcases p2578_3 (m.d 3 5) (by simp) with h2601 | h2601
                                                        · linarith only [h2518, h2601, hlam]
                                                        · linarith only [h1953, h2601, hlam]
                                                      · linarith only [h2600, hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                rcases p2578_3 (m.d 0 3) (by simp) with h2605 | h2605
                                                · linarith only [h2605, h7, hlam]
                                                · linarith only [h1, h2605, hlam]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                rcases p2578_3 (m.d 0 3) (by simp) with h2608 | h2608
                                                · linarith only [h2608, h7, hlam]
                                                · linarith only [h2608, h4, hlam]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h2134, h2518, h7, hc03, hc34, hlam, hphi, p2578_1]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                rcases p2578_3 (m.d 0 3) (by simp) with h2613 | h2613
                                                · linarith only [h2613, hlam, p2578_0]
                                                · rcases p2578_3 (m.d 1 3) (by simp) with h2615 | h2615
                                                  · linarith only [h2508, h2615, hlam]
                                                  · rcases p2578_3 (m.d 2 3) (by simp) with h2617 | h2617
                                                    · linarith only [h2514, h2617, hlam]
                                                    · rcases p2578_3 (m.d 3 4) (by simp) with h2619 | h2619
                                                      · rcases p2578_3 (m.d 3 5) (by simp) with h2620 | h2620
                                                        · rcases h4bigk with h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [hlam, p2621_0]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h0, h2134, h2503, h2506, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h0, h2134, h2512, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h7, hlam, p2621_0]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h2134, hlam, p2621_0]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h2, hlam, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [hlam, p2621_0]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h0, h2, h2134, h2512, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h2506, hlam, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h2510, hlam, p2621_0]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h5, hlam, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h2504, hlam, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [hlam, p2621_0]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h2512, hlam, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h2516, hlam, p2621_0]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            rcases p2621_3 (m.d 0 4) (by simp) with h2637 | h2637
                                                            · linarith only [h2637, h7, hlam]
                                                            · rcases p2621_3 (m.d 1 4) (by simp) with h2639 | h2639
                                                              · linarith only [h2506, h2639, hlam]
                                                              · rcases p2621_3 (m.d 2 4) (by simp) with h2641 | h2641
                                                                · linarith only [h2512, h2641, hlam]
                                                                · rcases p2621_3 (m.d 3 4) (by simp) with h2643 | h2643
                                                                  · rcases p2621_3 (m.d 4 5) (by simp) with h2644 | h2644
                                                                    · linarith only [h2518, h2644, hlam]
                                                                    · linarith only [h2134, h2644, hlam]
                                                                  · linarith only [h2643, h7, hlam]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            rcases p2621_3 (m.d 0 4) (by simp) with h2648 | h2648
                                                            · linarith only [h2648, h7, hlam]
                                                            · linarith only [h2, h2648, hlam]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            rcases p2621_3 (m.d 0 4) (by simp) with h2651 | h2651
                                                            · linarith only [h2651, h7, hlam]
                                                            · linarith only [h2651, h5, hlam]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [hlam, p2621_0]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h2134, h2512, h5, hc23, hc34, hlam, hphi, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h1, h2503, h2518, h7, hc23, hc34, hlam, hphi, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h2503, h2506, h2518, hc23, hc34, hlam, hphi, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h2512, h2518, hc23, hc34, hlam, hphi, p2621_1]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [h2518, hlam, p2621_0]
                                                          · have p2621_0 := h2621c.1
                                                            have p2621_1 := h2621c.2.1
                                                            have p2621_2 := h2621c.2.2.1
                                                            have p2621_3 := h2621c.2.2.2
                                                            linarith only [hlam, p2621_0]
                                                        · linarith only [h2620, hlam, p2578_0]
                                                      · linarith only [h2619, h7, hlam]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                rcases p2578_3 (m.d 0 3) (by simp) with h2663 | h2663
                                                · linarith only [h1953, h2663, hlam]
                                                · linarith only [h1, h2663, hlam]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                rcases p2578_3 (m.d 0 3) (by simp) with h2666 | h2666
                                                · linarith only [h1953, h2666, hlam]
                                                · linarith only [h2666, h4, hlam]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [h2518, hlam, p2578_0]
                                              · have p2578_0 := h2578c.1
                                                have p2578_1 := h2578c.2.1
                                                have p2578_2 := h2578c.2.2.1
                                                have p2578_3 := h2578c.2.2.2
                                                linarith only [hlam, p2578_0]
                                    · linarith only [h2569, hlam, p2567_0]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h0, h1, h2134, h7, hlam, p2519_1, p2567_2]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h0, h2, h2134, hlam, p2519_1, p2567_2]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h0, h3, hlam, p2519_1, p2567_2]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h0, hlam, p2567_0]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [hlam, p2567_0]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    rcases p2567_3 (m.d 0 1) (by simp) with h2677 | h2677
                                    · rcases p2567_3 (m.d 1 2) (by simp) with h2678 | h2678
                                      · rcases p2567_3 (m.d 1 3) (by simp) with h2679 | h2679
                                        · linarith only [h2503, h2679, hlam]
                                        · rcases p2567_3 (m.d 1 4) (by simp) with h2681 | h2681
                                          · linarith only [h2504, h2681, hlam]
                                          · linarith only [h2506, h2681, hlam]
                                      · linarith only [h2503, h2678, hlam]
                                    · linarith only [h1, h2677, hlam]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    rcases p2567_3 (m.d 0 1) (by simp) with h2686 | h2686
                                    · rcases p2567_3 (m.d 1 2) (by simp) with h2687 | h2687
                                      · rcases p2567_3 (m.d 1 3) (by simp) with h2688 | h2688
                                        · linarith only [h2503, h2688, hlam]
                                        · rcases p2567_3 (m.d 1 4) (by simp) with h2690 | h2690
                                          · linarith only [h2504, h2690, hlam]
                                          · rcases p2567_3 (m.d 1 5) (by simp) with h2692 | h2692
                                            · linarith only [h2505, h2692, hlam]
                                            · linarith only [h2510, h2692, hlam]
                                      · linarith only [h2504, h2687, hlam]
                                    · linarith only [h2, h2686, hlam]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    rcases p2567_3 (m.d 0 1) (by simp) with h2697 | h2697
                                    · rcases p2567_3 (m.d 1 2) (by simp) with h2698 | h2698
                                      · rcases p2567_3 (m.d 1 3) (by simp) with h2699 | h2699
                                        · linarith only [h2503, h2699, hlam]
                                        · rcases p2567_3 (m.d 1 4) (by simp) with h2701 | h2701
                                          · linarith only [h2504, h2701, hlam]
                                          · rcases p2567_3 (m.d 1 5) (by simp) with h2703 | h2703
                                            · linarith only [h2505, h2703, hlam]
                                            · rcases h3bigk with h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c | h2705c
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h0, h2134, h2503, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2705_1]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h0, h2134, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2705_1]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h7, hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h1953, hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h1, hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h0, h1, h2134, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2705_1]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h2506, hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h2508, hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h4, hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h2503, hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h2512, hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h2514, hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                rcases p2705_3 (m.d 0 3) (by simp) with h2721 | h2721
                                                · linarith only [h2721, hlam, p2705_0]
                                                · rcases p2705_3 (m.d 1 3) (by simp) with h2723 | h2723
                                                  · linarith only [h2506, h2723, hlam]
                                                  · rcases p2705_3 (m.d 2 3) (by simp) with h2725 | h2725
                                                    · linarith only [h2512, h2725, hlam]
                                                    · rcases p2705_3 (m.d 3 4) (by simp) with h2727 | h2727
                                                      · rcases p2705_3 (m.d 3 5) (by simp) with h2728 | h2728
                                                        · linarith only [h2518, h2728, hlam]
                                                        · linarith only [h1953, h2728, hlam]
                                                      · linarith only [h2727, hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                rcases p2705_3 (m.d 0 3) (by simp) with h2732 | h2732
                                                · linarith only [h2732, h7, hlam]
                                                · linarith only [h1, h2732, hlam]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                rcases p2705_3 (m.d 0 3) (by simp) with h2735 | h2735
                                                · linarith only [h2735, h7, hlam]
                                                · linarith only [h2735, h4, hlam]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h1953, hc03, hc34, hlam, hphi, p2705_1]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                rcases p2705_3 (m.d 0 3) (by simp) with h2740 | h2740
                                                · linarith only [h2740, hlam, p2705_0]
                                                · rcases p2705_3 (m.d 1 3) (by simp) with h2742 | h2742
                                                  · linarith only [h2508, h2742, hlam]
                                                  · rcases p2705_3 (m.d 2 3) (by simp) with h2744 | h2744
                                                    · linarith only [h2514, h2744, hlam]
                                                    · rcases p2705_3 (m.d 3 4) (by simp) with h2746 | h2746
                                                      · rcases p2705_3 (m.d 3 5) (by simp) with h2747 | h2747
                                                        · rcases h4bigk with h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [hlam, p2748_0]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h0, h2134, h2503, h2506, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h0, h2134, h2512, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h7, hlam, p2748_0]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h2134, hlam, p2748_0]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h2, hlam, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [hlam, p2748_0]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h0, h2, h2134, h2512, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h2506, hlam, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h2510, hlam, p2748_0]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h5, hlam, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h2504, hlam, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [hlam, p2748_0]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h2512, hlam, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h2516, hlam, p2748_0]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            rcases p2748_3 (m.d 0 4) (by simp) with h2764 | h2764
                                                            · linarith only [h2764, h7, hlam]
                                                            · rcases p2748_3 (m.d 1 4) (by simp) with h2766 | h2766
                                                              · linarith only [h2506, h2766, hlam]
                                                              · rcases p2748_3 (m.d 2 4) (by simp) with h2768 | h2768
                                                                · linarith only [h2512, h2768, hlam]
                                                                · rcases p2748_3 (m.d 3 4) (by simp) with h2770 | h2770
                                                                  · rcases p2748_3 (m.d 4 5) (by simp) with h2771 | h2771
                                                                    · linarith only [h2518, h2771, hlam]
                                                                    · linarith only [h2134, h2771, hlam]
                                                                  · linarith only [h2770, h7, hlam]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            rcases p2748_3 (m.d 0 4) (by simp) with h2775 | h2775
                                                            · linarith only [h2775, h7, hlam]
                                                            · linarith only [h2, h2775, hlam]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            rcases p2748_3 (m.d 0 4) (by simp) with h2778 | h2778
                                                            · linarith only [h2778, h7, hlam]
                                                            · linarith only [h2778, h5, hlam]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [hlam, p2748_0]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h2134, h2512, h5, hc23, hc34, hlam, hphi, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h1, h2503, h2518, h7, hc23, hc34, hlam, hphi, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h2504, h2512, h2518, hc23, hc34, hlam, hphi, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h2512, h2518, hc23, hc34, hlam, hphi, p2748_1]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [h2518, hlam, p2748_0]
                                                          · have p2748_0 := h2748c.1
                                                            have p2748_1 := h2748c.2.1
                                                            have p2748_2 := h2748c.2.2.1
                                                            have p2748_3 := h2748c.2.2.2
                                                            linarith only [hlam, p2748_0]
                                                        · linarith only [h2747, hlam, p2705_0]
                                                      · linarith only [h2746, h7, hlam]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                rcases p2705_3 (m.d 0 3) (by simp) with h2790 | h2790
                                                · linarith only [h1953, h2790, hlam]
                                                · linarith only [h1, h2790, hlam]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                rcases p2705_3 (m.d 0 3) (by simp) with h2793 | h2793
                                                · linarith only [h1953, h2793, hlam]
                                                · linarith only [h2793, h4, hlam]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [h2518, hlam, p2705_0]
                                              · have p2705_0 := h2705c.1
                                                have p2705_1 := h2705c.2.1
                                                have p2705_2 := h2705c.2.2.1
                                                have p2705_3 := h2705c.2.2.2
                                                linarith only [hlam, p2705_0]
                                      · linarith only [h2505, h2698, hlam]
                                    · linarith only [h2697, h3, hlam]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h1, hlam, p2567_0]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h2503, hlam, p2567_1]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [hlam, p2567_0]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h2506, hlam, p2567_1]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h2508, hlam, p2567_1]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h2, hlam, p2567_0]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h2504, hlam, p2567_1]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h0, h2, h2134, h2503, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2567_1]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [hlam, p2567_0]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h2510, hlam, p2567_1]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h3, hlam, p2567_0]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h2505, hlam, p2567_1]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h0, h2503, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2519_1, p2567_1]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [h0, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2519_1, p2567_1]
                                  · have p2567_0 := h2567c.1
                                    have p2567_1 := h2567c.2.1
                                    have p2567_2 := h2567c.2.2.1
                                    have p2567_3 := h2567c.2.2.2
                                    linarith only [hlam, p2567_0]
                          · linarith only [h2560, h6, hlam]
                        · linarith only [h2559, h3, hlam]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h1, hlam, p2519_1]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h4, hlam, p2519_1]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [hlam, p2519_0]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h7, hlam, p2519_1]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h1953, hlam, p2519_1]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h2, hlam, p2519_0]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h5, hlam, p2519_0]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h1, h2503, h7, hc23, hc34, hlam, hphi, p2519_1]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [hlam, p2519_0]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h2134, hlam, p2519_0]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h3, hlam, p2519_0]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h6, hlam, p2519_1]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h1, h1953, h2503, hc23, hc35, hlam, hphi, p2519_1]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [h1953, h2512, h5, hc23, hc35, hlam, hphi, p2519_1]
                      · have p2519_0 := h2519c.1
                        have p2519_1 := h2519c.2.1
                        have p2519_2 := h2519c.2.2.1
                        have p2519_3 := h2519c.2.2.2
                        linarith only [hlam, p2519_0]
                    · rcases h0bigk with h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c | h2832c
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [hlam, p2832_0]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h0, h2505, hc01, hc25, hlam, hphi, ht0b, ht5b, p2832_1]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        rcases p2832_3 (m.d 0 1) (by simp) with h2835 | h2835
                        · rcases p2832_3 (m.d 0 2) (by simp) with h2836 | h2836
                          · linarith only [h0, h2836, hlam]
                          · linarith only [h2836, h4, hlam]
                        · linarith only [h1, h2835, hlam]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        rcases p2832_3 (m.d 0 1) (by simp) with h2840 | h2840
                        · rcases p2832_3 (m.d 0 2) (by simp) with h2841 | h2841
                          · linarith only [h0, h2841, hlam]
                          · linarith only [h2841, h5, hlam]
                        · linarith only [h2, h2840, hlam]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        rcases p2832_3 (m.d 0 1) (by simp) with h2845 | h2845
                        · rcases p2832_3 (m.d 0 2) (by simp) with h2846 | h2846
                          · linarith only [h0, h2846, hlam]
                          · linarith only [h2846, h6, hlam]
                        · linarith only [h2845, h3, hlam]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h0, hlam, p2832_0]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [hlam, p2832_0]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        rcases p2832_3 (m.d 0 1) (by simp) with h2852 | h2852
                        · rcases p2832_3 (m.d 0 2) (by simp) with h2853 | h2853
                          · rcases p2832_3 (m.d 0 3) (by simp) with h2854 | h2854
                            · linarith only [h2854, h4, hlam]
                            · rcases p2832_3 (m.d 0 4) (by simp) with h2856 | h2856
                              · linarith only [h2856, h5, hlam]
                              · linarith only [h2856, h7, hlam]
                          · linarith only [h2853, h4, hlam]
                        · linarith only [h1, h2852, hlam]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        rcases p2832_3 (m.d 0 1) (by simp) with h2861 | h2861
                        · rcases p2832_3 (m.d 0 2) (by simp) with h2862 | h2862
                          · rcases p2832_3 (m.d 0 3) (by simp) with h2863 | h2863
                            · linarith only [h2863, h4, hlam]
                            · rcases p2832_3 (m.d 0 4) (by simp) with h2865 | h2865
                              · linarith only [h2865, h5, hlam]
                              · rcases p2832_3 (m.d 0 5) (by simp) with h2867 | h2867
                                · linarith only [h2867, h6, hlam]
                                · linarith only [h2134, h2867, hlam]
                          · linarith only [h2862, h5, hlam]
                        · linarith only [h2, h2861, hlam]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        rcases p2832_3 (m.d 0 1) (by simp) with h2872 | h2872
                        · rcases p2832_3 (m.d 0 2) (by simp) with h2873 | h2873
                          · rcases p2832_3 (m.d 0 3) (by simp) with h2874 | h2874
                            · linarith only [h2874, h4, hlam]
                            · rcases p2832_3 (m.d 0 4) (by simp) with h2876 | h2876
                              · linarith only [h2876, h5, hlam]
                              · rcases p2832_3 (m.d 0 5) (by simp) with h2878 | h2878
                                · linarith only [h2878, h6, hlam]
                                · rcases h1bigk with h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c | h2880c
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [hlam, p2880_0]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    rcases p2880_3 (m.d 0 1) (by simp) with h2882 | h2882
                                    · rcases p2880_3 (m.d 1 2) (by simp) with h2883 | h2883
                                      · linarith only [h2883, hlam, p2880_0]
                                      · rcases p2880_3 (m.d 1 3) (by simp) with h2885 | h2885
                                        · linarith only [h1, h2885, hlam]
                                        · rcases p2880_3 (m.d 1 4) (by simp) with h2887 | h2887
                                          · linarith only [h2, h2887, hlam]
                                          · rcases p2880_3 (m.d 1 5) (by simp) with h2889 | h2889
                                            · linarith only [h2889, h3, hlam]
                                            · rcases h3bigk with h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h2503, h2518, h7, hc23, hc45, hlam, hphi, ht34, p2891_1]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h2518, h7, hc23, hc45, hlam, hphi, ht34, p2891_1]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h7, hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h1953, hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h1, hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h1, h2518, h7, hc23, hc45, hlam, hphi, ht34, p2891_1]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h2506, hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h2508, hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h4, hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h2503, hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h2512, hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h2514, hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h2518, hc03, hc45, hlam, hphi, ht34, p2891_1]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h2503, h2518, hc23, hc45, hlam, hphi, ht34, p2891_1]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h2518, hc23, hc45, hlam, hphi, ht34, p2891_1]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [hlam, p2891_0]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h2518, hlam, p2891_1]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                rcases p2891_3 (m.d 0 3) (by simp) with h2912 | h2912
                                                · linarith only [h2912, hlam, p2891_0]
                                                · rcases p2891_3 (m.d 1 3) (by simp) with h2914 | h2914
                                                  · linarith only [h2508, h2914, hlam]
                                                  · rcases p2891_3 (m.d 2 3) (by simp) with h2916 | h2916
                                                    · linarith only [h2514, h2916, hlam]
                                                    · rcases p2891_3 (m.d 3 4) (by simp) with h2918 | h2918
                                                      · linarith only [h2518, h2918, hlam]
                                                      · linarith only [h2918, h7, hlam]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                rcases p2891_3 (m.d 0 3) (by simp) with h2921 | h2921
                                                · linarith only [h1953, h2921, hlam]
                                                · linarith only [h1, h2921, hlam]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                rcases p2891_3 (m.d 0 3) (by simp) with h2924 | h2924
                                                · linarith only [h1953, h2924, hlam]
                                                · linarith only [h2924, h4, hlam]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [h1, h2503, h2518, h7, hc23, hc45, hlam, hphi, ht34, p2891_1]
                                              · have p2891_0 := h2891c.1
                                                have p2891_1 := h2891c.2.1
                                                have p2891_2 := h2891c.2.2.1
                                                have p2891_3 := h2891c.2.2.2
                                                linarith only [hlam, p2891_0]
                                    · linarith only [h2882, hlam, p2880_0]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h0, h1, h1953, hlam, p2832_1, p2880_2]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h0, h2, h2134, hlam, p2832_1, p2880_2]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h0, h3, hlam, p2832_1, p2880_2]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h0, hlam, p2880_0]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [hlam, p2880_0]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    rcases p2880_3 (m.d 0 1) (by simp) with h2935 | h2935
                                    · rcases p2880_3 (m.d 1 2) (by simp) with h2936 | h2936
                                      · rcases p2880_3 (m.d 1 3) (by simp) with h2937 | h2937
                                        · linarith only [h2503, h2937, hlam]
                                        · rcases p2880_3 (m.d 1 4) (by simp) with h2939 | h2939
                                          · linarith only [h2504, h2939, hlam]
                                          · linarith only [h2506, h2939, hlam]
                                      · linarith only [h2503, h2936, hlam]
                                    · linarith only [h1, h2935, hlam]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    rcases p2880_3 (m.d 0 1) (by simp) with h2944 | h2944
                                    · rcases p2880_3 (m.d 1 2) (by simp) with h2945 | h2945
                                      · rcases p2880_3 (m.d 1 3) (by simp) with h2946 | h2946
                                        · linarith only [h2503, h2946, hlam]
                                        · rcases p2880_3 (m.d 1 4) (by simp) with h2948 | h2948
                                          · linarith only [h2504, h2948, hlam]
                                          · rcases p2880_3 (m.d 1 5) (by simp) with h2950 | h2950
                                            · linarith only [h2505, h2950, hlam]
                                            · linarith only [h2510, h2950, hlam]
                                      · linarith only [h2504, h2945, hlam]
                                    · linarith only [h2, h2944, hlam]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    rcases p2880_3 (m.d 0 1) (by simp) with h2955 | h2955
                                    · rcases p2880_3 (m.d 1 2) (by simp) with h2956 | h2956
                                      · rcases p2880_3 (m.d 1 3) (by simp) with h2957 | h2957
                                        · linarith only [h2503, h2957, hlam]
                                        · rcases p2880_3 (m.d 1 4) (by simp) with h2959 | h2959
                                          · linarith only [h2504, h2959, hlam]
                                          · rcases p2880_3 (m.d 1 5) (by simp) with h2961 | h2961
                                            · linarith only [h2505, h2961, hlam]
                                            · rcases h3bigk with h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h0, h2134, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2832_1, p2963_1]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h0, h2134, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2832_1, p2963_1]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h7, hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h1953, hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h1, hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h0, h1, h2134, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2832_1, p2963_1]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h2506, hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h2508, hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h4, hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h2503, hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h2512, hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h2514, hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h2518, hc03, hc45, hlam, hphi, ht34, p2963_1]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h2503, h2518, hc23, hc45, hlam, hphi, ht34, p2963_1]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h2518, hc23, hc45, hlam, hphi, ht34, p2963_1]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [hlam, p2963_0]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h2518, hlam, p2963_1]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                rcases p2963_3 (m.d 0 3) (by simp) with h2984 | h2984
                                                · linarith only [h2984, hlam, p2963_0]
                                                · rcases p2963_3 (m.d 1 3) (by simp) with h2986 | h2986
                                                  · linarith only [h2508, h2986, hlam]
                                                  · rcases p2963_3 (m.d 2 3) (by simp) with h2988 | h2988
                                                    · linarith only [h2514, h2988, hlam]
                                                    · rcases p2963_3 (m.d 3 4) (by simp) with h2990 | h2990
                                                      · linarith only [h2518, h2990, hlam]
                                                      · linarith only [h2990, h7, hlam]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                rcases p2963_3 (m.d 0 3) (by simp) with h2993 | h2993
                                                · linarith only [h1953, h2993, hlam]
                                                · linarith only [h1, h2993, hlam]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                rcases p2963_3 (m.d 0 3) (by simp) with h2996 | h2996
                                                · linarith only [h1953, h2996, hlam]
                                                · linarith only [h2996, h4, hlam]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [h1, h2503, h2518, h7, hc23, hc45, hlam, hphi, ht34, p2963_1]
                                              · have p2963_0 := h2963c.1
                                                have p2963_1 := h2963c.2.1
                                                have p2963_2 := h2963c.2.2.1
                                                have p2963_3 := h2963c.2.2.2
                                                linarith only [hlam, p2963_0]
                                      · linarith only [h2505, h2956, hlam]
                                    · linarith only [h2955, h3, hlam]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h1, hlam, p2880_0]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h2503, hlam, p2880_1]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [hlam, p2880_0]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h2506, hlam, p2880_1]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h2508, hlam, p2880_1]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h2, hlam, p2880_0]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h2504, hlam, p2880_1]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h0, h2, h2134, h2503, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2832_1, p2880_1]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [hlam, p2880_0]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h2510, hlam, p2880_1]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h3, hlam, p2880_0]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h2505, hlam, p2880_1]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h0, h2503, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2832_1, p2880_1]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [h0, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2832_1, p2880_1]
                                  · have p2880_0 := h2880c.1
                                    have p2880_1 := h2880c.2.1
                                    have p2880_2 := h2880c.2.2.1
                                    have p2880_3 := h2880c.2.2.2
                                    linarith only [hlam, p2880_0]
                          · linarith only [h2873, h6, hlam]
                        · linarith only [h2872, h3, hlam]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h1, hlam, p2832_1]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h4, hlam, p2832_1]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [hlam, p2832_0]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h7, hlam, p2832_1]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h1953, hlam, p2832_1]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h2, hlam, p2832_0]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h5, hlam, p2832_0]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h1, h2503, h7, hc23, hc34, hlam, hphi, p2832_1]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [hlam, p2832_0]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h2134, hlam, p2832_0]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h3, hlam, p2832_0]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h6, hlam, p2832_1]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h1, h1953, h2503, h2518, hc23, hc45, hlam, hphi, ht34, p2832_1]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [h1953, h2518, hc04, hc45, hlam, hphi, p2832_1]
                      · have p2832_0 := h2832c.1
                        have p2832_1 := h2832c.2.1
                        have p2832_2 := h2832c.2.2.1
                        have p2832_3 := h2832c.2.2.2
                        linarith only [hlam, p2832_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3035 | h3035
        · linarith only [h1, h3035, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3037 | h3037
          · linarith only [h1, h1953, h2505, h3037, h6, h7, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3039 | h3039
            · linarith only [h0, h2134, h2504, h2505, h3039, h6, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3041 | h3041
              · linarith only [h2134, h2503, h2505, h3041, h6, hc34, hc45, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3043 | h3043
                · linarith only [h0, h2504, h2505, h3041, h3043, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3045 | h3045
                  · linarith only [h2134, h2504, h2505, h3045, h6, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3047 | h3047
                    · linarith only [h2134, h2504, h2505, h3041, h3047, h6, hc23, hc34, hlam, hphi]
                    · rcases h0bigk with h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c | h3049c
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [hlam, p3049_0]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h2504, h2505, h3041, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3049_1]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        rcases p3049_3 (m.d 0 1) (by simp) with h3052 | h3052
                        · rcases p3049_3 (m.d 0 2) (by simp) with h3053 | h3053
                          · linarith only [h0, h3053, hlam]
                          · linarith only [h3053, h4, hlam]
                        · linarith only [h1, h3052, hlam]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        rcases p3049_3 (m.d 0 1) (by simp) with h3057 | h3057
                        · rcases p3049_3 (m.d 0 2) (by simp) with h3058 | h3058
                          · linarith only [h0, h3058, hlam]
                          · linarith only [h3058, h5, hlam]
                        · linarith only [h2, h3057, hlam]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h2504, h2505, h3041, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3049_1]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h0, hlam, p3049_0]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [hlam, p3049_0]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        rcases p3049_3 (m.d 0 1) (by simp) with h3065 | h3065
                        · rcases p3049_3 (m.d 0 2) (by simp) with h3066 | h3066
                          · rcases p3049_3 (m.d 0 3) (by simp) with h3067 | h3067
                            · linarith only [h3067, h4, hlam]
                            · rcases p3049_3 (m.d 0 4) (by simp) with h3069 | h3069
                              · linarith only [h3069, h5, hlam]
                              · linarith only [h3069, h7, hlam]
                          · linarith only [h3066, h4, hlam]
                        · linarith only [h1, h3065, hlam]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        rcases p3049_3 (m.d 0 1) (by simp) with h3074 | h3074
                        · rcases p3049_3 (m.d 0 2) (by simp) with h3075 | h3075
                          · rcases p3049_3 (m.d 0 3) (by simp) with h3076 | h3076
                            · linarith only [h3076, h4, hlam]
                            · rcases p3049_3 (m.d 0 4) (by simp) with h3078 | h3078
                              · linarith only [h3078, h5, hlam]
                              · rcases p3049_3 (m.d 0 5) (by simp) with h3080 | h3080
                                · linarith only [h3080, h6, hlam]
                                · linarith only [h2134, h3080, hlam]
                          · linarith only [h3075, h5, hlam]
                        · linarith only [h2, h3074, hlam]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h2504, h2505, h3041, h6, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3049_1]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h1, hlam, p3049_1]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h4, hlam, p3049_1]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [hlam, p3049_0]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h7, hlam, p3049_1]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h1953, hlam, p3049_1]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h2, hlam, p3049_0]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h5, hlam, p3049_0]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h1, h2503, h3047, h7, hc23, hc45, hlam, hphi, ht34, p3049_1]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [hlam, p3049_0]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h2134, hlam, p3049_0]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h3, hlam, p3049_0]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h6, hlam, p3049_1]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h1, h1953, h2503, hc23, hc35, hlam, hphi, p3049_1]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [h2134, hc04, hc45, hlam, hphi, p3049_1]
                      · have p3049_0 := h3049c.1
                        have p3049_1 := h3049c.2.1
                        have p3049_2 := h3049c.2.2.1
                        have p3049_3 := h3049c.2.2.2
                        linarith only [hlam, p3049_0]
    · linarith only [h2134, h2503, h2504, h5, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h3102 | h3102
    · linarith only [h2134, h2503, h3102, h4, h7, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3104 | h3104
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3105 | h3105
        · linarith only [h2503, h3104, h3105, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3107 | h3107
          · linarith only [h1953, h2503, h3104, h3107, h4, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h2503, h3104, h3107, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3110 | h3110
        · linarith only [h1, h2503, h3110, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3112 | h3112
          · linarith only [h1953, h2503, h3104, h3112, h4, h6, h7, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3114 | h3114
            · linarith only [h2134, h3102, h3114, h5, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3116 | h3116
              · linarith only [h3116, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3118 | h3118
                · linarith only [h1953, h3118, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3120 | h3120
                  · linarith only [h2134, h3120, h5, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3122 | h3122
                    · linarith only [h2134, h2503, h3122, h4, h7, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h2503, h3122, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h1953 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h2134 | h2134
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h1953 h2134
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h1953 h2134

set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h1953 | h1953
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h1953
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h1953

set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7

set_option maxHeartbeats 6402000 in
set_option maxHeartbeats 6402000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s5 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5 h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3125 | h3125
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3126 | h3126
      · linarith only [h3126, h4, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3128 | h3128
        · linarith only [h3128, h5, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3130 | h3130
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3131 | h3131
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3132 | h3132
              · linarith only [h0, h3125, h3132, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3134 | h3134
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3135 | h3135
                  · linarith only [h1, h3126, h3135, h4, h6, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3137 | h3137
                    · linarith only [h2, h3128, h3137, h5, h6, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3139 | h3139
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3140 | h3140
                        · linarith only [h0, h1, h3126, h3130, h3140, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3142 | h3142
                          · linarith only [h3128, h3139, h3142, h4, h6, hlam]
                          · linarith only [h0, h3130, h3139, h3142, h6, hc34, hc45, hlam, hphi]
                      · linarith only [h3125, h3126, h3139, hc23, hc35, hlam, hphi]
                · linarith only [h3125, h3126, h3134, hc13, hc35, hlam, hphi]
            · linarith only [h3131, h5, h6, hc12, hc25, hlam, hphi]
          · linarith only [h3130, h4, h6, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3149 | h3149
      · linarith only [h3149, h4, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3151 | h3151
        · linarith only [h3151, h5, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3153 | h3153
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3154 | h3154
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3155 | h3155
              · linarith only [h0, h3155, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3157 | h3157
                · linarith only [h1, h3125, h3157, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3159 | h3159
                  · linarith only [h1, h3149, h3159, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3161 | h3161
                    · linarith only [h2, h3151, h3161, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3163 | h3163
                      · linarith only [h3125, h3163, h4, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3165 | h3165
                        · linarith only [h0, h3149, h3154, h3163, h3165, h6, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3167 | h3167
                          · linarith only [h0, h3151, h3154, h3167, h6, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3169 | h3169
                            · linarith only [h0, h3154, h3163, h3167, h3169, h6, hc23, hc34, hlam, hphi]
                            · rcases h0bigk with h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h0, h3154, h3163, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                rcases p3171_3 (m.d 0 1) (by simp) with h3174 | h3174
                                · rcases p3171_3 (m.d 0 2) (by simp) with h3175 | h3175
                                  · linarith only [h0, h3175, hlam]
                                  · linarith only [h3175, h4, hlam]
                                · linarith only [h1, h3174, hlam]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                rcases p3171_3 (m.d 0 1) (by simp) with h3179 | h3179
                                · rcases p3171_3 (m.d 0 2) (by simp) with h3180 | h3180
                                  · linarith only [h0, h3180, hlam]
                                  · linarith only [h3180, h5, hlam]
                                · linarith only [h2, h3179, hlam]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h0, h3154, h3163, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h0, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h6, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h1, h3125, h3153, h3165, h6, hc23, hc35, hlam, hphi, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h6, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h1, hlam, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h4, hlam, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h3125, hlam, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h3149, hlam, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h2, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h5, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h1, h3153, h3165, h5, h6, hc23, hc35, hlam, hphi, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h3151, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h3, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h0, h3154, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h1, h3149, h3153, hc23, hc35, hlam, hphi, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h3151, hc04, hc45, hlam, hphi, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [hlam, p3171_0]
            · linarith only [h3153, h3154, h5, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h3153, h4, h6, hc12, hc25, hlam, hphi]

end R2N4
