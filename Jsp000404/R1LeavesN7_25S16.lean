import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5352000 in
set_option maxHeartbeats 5352000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s2 m hb0 hb2 hb3 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2525 | h2525
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2526 | h2526
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2527 | h2527
        · linarith only [h0, h2, h2527, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2529 | h2529
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2530 | h2530
            · linarith only [h1, h2, h2530, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2532 | h2532
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2533 | h2533
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2534 | h2534
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2535 | h2535
                    · linarith only [h0, h2, h2527, h2535, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2537 | h2537
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2538 | h2538
                        · linarith only [h1, h2, h2530, h2538, hlam]
                        · linarith only [h0, h2, h2534, h2538, hc23, hc34, hlam, hphi]
                      · linarith only [h2534, h2537, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h2526, h2527, h2534, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h2533, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2544 | h2544
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2545 | h2545
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2546 | h2546
                    · linarith only [h0, h2527, h2546, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2548 | h2548
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2549 | h2549
                        · linarith only [h0, h1, h2, h2530, h2532, h2549, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                        · linarith only [h0, h2, h2545, h2549, hc23, hc34, hlam, hphi]
                      · linarith only [h2545, h2548, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h2526, h2532, h2545, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h2, h2544, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
          · linarith only [h2526, h2529, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2556 | h2556
        · linarith only [h0, h2, h2556, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2558 | h2558
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2559 | h2559
            · linarith only [h1, h2, h2559, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2561 | h2561
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2562 | h2562
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2563 | h2563
                  · linarith only [h0, h2, h2526, h2563, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2565 | h2565
                    · linarith only [h0, h2, h2556, h2565, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2567 | h2567
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2568 | h2568
                        · linarith only [h1, h2, h2559, h2568, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2570 | h2570
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2571 | h2571
                            · linarith only [h0, h2, h2567, h2568, h2571, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2573 | h2573
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2574 | h2574
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2575 | h2575
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
                                      linarith only [h0, h2567, h2573, h2575, hc01, hc45, hlam, hphi, ht0b, ht5b, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h0, h2, h2526, h2565, h2567, h2571, h2573, h2575, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h2, hlam, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h2, h2565, h2571, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h0, hlam, p2576_0]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [hlam, p2576_0]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h2526, hlam, p2576_0]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h2556, hlam, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h0, h2, h2525, h2565, h2567, h2571, h2573, h2575, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h1, hlam, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h0, h2567, h2573, h2575, hc03, hc45, hlam, hphi, ht0b, ht5b, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [hlam, p2576_0]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h2559, hlam, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h1, h2, h2525, h2565, h2567, h2571, h2573, h2575, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h2, h2565, h2571, hc01, hc34, hlam, hphi, ht12, ht23, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h0, h2, h2565, h2567, h2571, h2573, h2575, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h2, h2565, h2571, hc03, hc34, hlam, hphi, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [hlam, p2576_0]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      rcases p2576_3 (m.d 0 1) (by simp) with h2596 | h2596
                                      · linarith only [h2, h2596, hlam]
                                      · linarith only [h2525, h2596, hlam]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h2525, hlam, p2576_0]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h2558, hlam, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h2561, hlam, p2576_0]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [h2562, hlam, p2576_1]
                                    · have p2576_0 := h2576c.1
                                      have p2576_1 := h2576c.2.1
                                      have p2576_2 := h2576c.2.2.1
                                      have p2576_3 := h2576c.2.2.2
                                      linarith only [hlam, p2576_0]
                                  · linarith only [h2571, h2575, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                · linarith only [h1, h2, h2525, h2563, h2565, h2567, h2570, h2574, hc05, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h2526, h2567, h2573, hc25, hlam, hphi, u5elo3]
                          · linarith only [h1, h2, h2563, h2567, h2570, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h1, h2, h2526, h2558, h2565, h2567, hc12, hc24, hlam, hphi]
                · linarith only [h2, h2525, h2562, hc15, hlam, hphi, u5elo4]
              · linarith only [h2526, h2558, h2561, hc25, hlam, hphi, u5elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2611 | h2611
            · linarith only [h1, h2, h2611, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2613 | h2613
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2614 | h2614
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2615 | h2615
                  · linarith only [h0, h2558, h2615, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2617 | h2617
                    · linarith only [h0, h2558, h2617, hc24, hlam, hphi, ht45, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2619 | h2619
                      · linarith only [h0, h2558, h2619, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2621 | h2621
                        · linarith only [h1, h2, h2611, h2621, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2623 | h2623
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2624 | h2624
                            · linarith only [h0, h2, h2621, h2624, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2626 | h2626
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2627 | h2627
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2628 | h2628
                                  · rcases h0bigk with h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [hlam, p2629_0]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h2, hlam, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h0, h2, h2558, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h0, hlam, p2629_0]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [hlam, p2629_0]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h2526, hlam, p2629_0]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h2556, hlam, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h2558, hlam, p2629_0]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h1, hlam, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [hlam, p2629_0]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h2611, hlam, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h0, h2526, h2558, hc12, hc23, hlam, hphi, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h1, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h0, h2556, hc12, hc24, hlam, hphi, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h2611, hc03, hc34, hlam, hphi, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [hlam, p2629_0]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h0, h2558, h2611, hc12, hc34, hlam, hphi, ht23, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h2525, hlam, p2629_0]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p2629_1, u5elo0]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h2613, hlam, p2629_0]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [h2614, hlam, p2629_1]
                                    · have p2629_0 := h2629c.1
                                      have p2629_1 := h2629c.2.1
                                      have p2629_2 := h2629c.2.2.1
                                      have p2629_3 := h2629c.2.2.2
                                      linarith only [hlam, p2629_0]
                                  · linarith only [h2624, h2628, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                · linarith only [h2, h2525, h2617, h2623, h2627, hlam]
                              · linarith only [h0, h1, h2, h2526, h2613, h2617, h2626, hc12, hc24, hlam, hphi]
                          · linarith only [h2, h2623, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h2, h2525, h2614, hc15, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2660 | h2660
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2661 | h2661
                  · linarith only [h0, h2526, h2661, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2663 | h2663
                    · linarith only [h1, h2, h2556, h2661, h2663, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2665 | h2665
                      · linarith only [h1, h2613, h2661, h2665, hc25, hlam, hphi, u5elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2667 | h2667
                        · linarith only [h1, h2, h2611, h2613, h2667, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2669 | h2669
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2670 | h2670
                            · linarith only [h1, h2, h2661, h2667, h2670, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2672 | h2672
                              · linarith only [h2613, h2670, h2672, hc03, hc34, hlam, hphi]
                              · linarith only [h0, h2526, h2672, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                          · linarith only [h1, h2, h2661, h2669, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h1, h2, h2660, hc13, hlam, hphi, ht34, ht45, u5elo4]
    · linarith only [h0, h2525, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 6188000 in
set_option maxHeartbeats 6188000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s1 m hb0 hb2 hb3 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2678 | h2678
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2679 | h2679
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2680 | h2680
        · linarith only [h0, h1, h2680, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2682 | h2682
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2683 | h2683
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2684 | h2684
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2685 | h2685
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2686 | h2686
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2687 | h2687
                    · linarith only [h0, h1, h2680, h2687, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2689 | h2689
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2690 | h2690
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2691 | h2691
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2692 | h2692
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2693 | h2693
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2694 | h2694
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2695 | h2695
                                  · linarith only [h0, h1, h2687, h2689, h2695, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h0, h1, h2687, h2689, h2692, h2695, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h1, h2687, h2694, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h2687, h2689, h2692, h2693, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2700 | h2700
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2701 | h2701
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2702 | h2702
                                  · linarith only [h2689, h2692, h2702, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2704 | h2704
                                    · linarith only [h2689, h2692, h2700, h2704, hlam]
                                    · rcases h0bigk with h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h2682, h2686, h2689, h2692, h2700, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h1, hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h1, h2686, h2687, h2689, h2692, h2700, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h1, h2686, h2687, h2689, h2692, h2700, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h0, hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h2680, hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h2686, h2689, h2692, h2700, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h0, h1, h2686, h2687, h2689, h2692, h2700, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h1, h2687, hc01, hc23, hlam, hphi, ht12, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h1, h2687, hc02, hc23, hlam, hphi, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h1, h2686, h2687, h2689, h2692, h2700, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h1, h2686, h2687, h2689, h2692, h2700, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h2678, hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h2682, hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h2684, hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h0, h2682, h2686, h2689, h2692, h2700, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h2679, hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h2683, hlam, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h2685, hlam, p2706_0]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [h2686, hlam, p2706_1]
                                      · have p2706_0 := h2706c.1
                                        have p2706_1 := h2706c.2.1
                                        have p2706_2 := h2706c.2.2.1
                                        have p2706_3 := h2706c.2.2.2
                                        linarith only [hlam, p2706_0]
                                · linarith only [h1, h2687, h2701, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                              · linarith only [h0, h1, h2682, h2686, h2687, h2689, h2692, h2700, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h2682, h2684, h2691, hlam]
                        · linarith only [h0, h1, h2683, h2687, h2690, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h2682, h2687, h2689, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2737 | h2737
                    · linarith only [h0, h1, h2680, h2737, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2739 | h2739
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2740 | h2740
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2741 | h2741
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2742 | h2742
                            · linarith only [h1, h2678, h2686, h2737, h2742, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2744 | h2744
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2745 | h2745
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2746 | h2746
                                  · linarith only [h0, h1, h2686, h2737, h2739, h2746, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2748 | h2748
                                    · linarith only [h2684, h2686, h2748, hlam]
                                    · rcases h0bigk with h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h0, h2740, h2746, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2750_1]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h1, hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h1, h2737, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2750_1]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h1, h2737, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2750_1]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h0, hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h2680, hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h0, h1, h2678, h2737, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2750_1]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h0, h1, h2679, h2737, h2742, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2750_1]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h1, h2737, hc01, hc23, hlam, hphi, ht12, p2750_1]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h1, h2737, hc02, hc23, hlam, hphi, p2750_1]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        rcases p2750_3 (m.d 0 1) (by simp) with h2764 | h2764
                                        · linarith only [h1, h2764, hlam]
                                        · linarith only [h2678, h2764, hlam]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        rcases p2750_3 (m.d 0 1) (by simp) with h2767 | h2767
                                        · linarith only [h1, h2767, hlam]
                                        · linarith only [h2679, h2767, hlam]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h2678, hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h2682, hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h2684, hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h2686, hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h2679, hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h2683, hlam, p2750_1]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h2685, hlam, p2750_0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [h2678, h2739, h2744, hc34, hlam, hphi, ht45, p2750_1, u5elo0]
                                      · have p2750_0 := h2750c.1
                                        have p2750_1 := h2750c.2.1
                                        have p2750_2 := h2750c.2.2.1
                                        have p2750_3 := h2750c.2.2.2
                                        linarith only [hlam, p2750_0]
                                · linarith only [h1, h2737, h2745, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                              · linarith only [h0, h1, h2737, h2739, h2744, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h2684, h2739, h2741, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h2739, h2740, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h0, h1, h2682, h2737, h2739, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h2685, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h1, h2678, h2684, hlam]
            · linarith only [h2682, h2683, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2788 | h2788
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2789 | h2789
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2790 | h2790
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2791 | h2791
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2792 | h2792
                    · linarith only [h0, h2680, h2788, h2792, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2794 | h2794
                      · linarith only [h0, h2682, h2794, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2796 | h2796
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2797 | h2797
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2798 | h2798
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2799 | h2799
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2800 | h2800
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2801 | h2801
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2802 | h2802
                                    · rcases h0bigk with h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c | h2803c
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [hlam, p2803_0]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h0, h1, h2792, h2796, h2800, h2802, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h1, hlam, p2803_0]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h0, h1, h2682, h2792, h2796, h2800, h2802, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h1, h2792, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h0, hlam, p2803_0]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [hlam, p2803_0]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h2680, hlam, p2803_0]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h2682, hlam, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h2679, h2682, h2796, h2800, h2802, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h1, h2792, hc01, hc23, hlam, hphi, ht12, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h1, h2792, hc02, hc23, hlam, hphi, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [hlam, p2803_0]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h0, h1, h2682, h2792, h2796, h2800, h2802, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        rcases p2803_3 (m.d 0 1) (by simp) with h2818 | h2818
                                        · linarith only [h1, h2818, hlam]
                                        · linarith only [h2679, h2818, hlam]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h2678, hlam, p2803_0]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h0, h2796, h2800, h2802, hc04, hc45, hlam, hphi, ht0b, ht5b, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h2789, hlam, p2803_0]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [hlam, p2803_0]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h1, h2678, h2679, h2792, h2796, h2800, h2802, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h2679, hlam, p2803_0]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h2788, hlam, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h2790, hlam, p2803_0]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [h2791, hlam, p2803_1]
                                      · have p2803_0 := h2803c.1
                                        have p2803_1 := h2803c.2.1
                                        have p2803_2 := h2803c.2.2.1
                                        have p2803_3 := h2803c.2.2.2
                                        linarith only [hlam, p2803_0]
                                    · linarith only [h1, h2678, h2792, h2798, h2802, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h2679, h2682, h2796, h2798, h2800, h2801, hc35, hlam, hphi, u5elo0]
                                · linarith only [h1, h2678, h2792, h2798, h2800, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h2678, h2792, h2794, h2796, h2799, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h2794, h2796, h2798, hc25, hlam, hphi, u5elo4]
                          · linarith only [h1, h2678, h2794, h2796, h2797, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h2678, h2682, h2788, h2792, h2796, hc12, hc23, hlam, hphi]
                  · linarith only [h2682, h2788, h2791, hc25, hlam, hphi, u5elo4]
                · linarith only [h0, h1, h2790, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h1, h2678, h2789, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2841 | h2841
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2842 | h2842
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2843 | h2843
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2844 | h2844
                    · linarith only [h0, h2788, h2844, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2846 | h2846
                      · linarith only [h0, h2682, h2846, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2848 | h2848
                        · linarith only [h0, h2788, h2848, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2850 | h2850
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
                                        linarith only [h1, h2844, hc02, hc23, hlam, hphi, p2856_1]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h1, hlam, p2856_0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h1, h2678, h2844, h2850, h2855, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2856_1]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h0, h1, h2788, h2844, hc12, hc23, hlam, hphi, p2856_1]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h0, hlam, p2856_0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [hlam, p2856_0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h2680, hlam, p2856_0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h2682, hlam, p2856_1]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h2788, hlam, p2856_0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2856_1]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h0, h1, h2844, hc12, hc23, hlam, hphi, p2856_1]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [hlam, p2856_0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h1, h2678, h2844, h2850, h2855, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2856_1]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h0, h1, h2788, h2844, hc12, hc23, hlam, hphi, p2856_1]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h2678, hlam, p2856_0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h0, h1, h2678, h2844, hc12, hc23, hlam, hphi, p2856_1]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h2841, hlam, p2856_0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [hlam, p2856_0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h0, h1, h2678, h2788, h2844, hc12, hc23, hlam, hphi, p2856_1]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h2679, hlam, p2856_0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p2856_1, u5elo0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h2842, hlam, p2856_0]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [h2843, hlam, p2856_1]
                                      · have p2856_0 := h2856c.1
                                        have p2856_1 := h2856c.2.1
                                        have p2856_2 := h2856c.2.2.1
                                        have p2856_3 := h2856c.2.2.2
                                        linarith only [hlam, p2856_0]
                                    · linarith only [h1, h2678, h2844, h2851, h2855, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h2678, h2682, h2844, h2851, h2854, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h1, h2788, h2842, h2844, h2853, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                              · linarith only [h0, h1, h2844, h2852, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h2678, h2843, h2844, h2846, h2851, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h2850, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2888 | h2888
                    · linarith only [h0, h1, h2680, h2888, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2890 | h2890
                      · linarith only [h0, h2682, h2890, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2892 | h2892
                        · linarith only [h0, h2679, h2682, h2788, h2843, h2892, hc15, hlam, hphi, u5elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2894 | h2894
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2895 | h2895
                            · linarith only [h2678, h2843, h2895, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2897 | h2897
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2898 | h2898
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2899 | h2899
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2900 | h2900
                                    · linarith only [h2678, h2843, h2894, h2900, hlam]
                                    · rcases h0bigk with h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h0, h1, h2888, hc12, hc23, hlam, hphi, p2902_1]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h1, hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h0, h1, h2682, h2888, hc12, hc23, hlam, hphi, p2902_1]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h0, h1, h2682, h2843, h2888, hc12, hc23, hlam, hphi, p2902_1]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h0, hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h2680, hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h2682, hlam, p2902_1]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h2788, hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2902_1]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h1, h2888, hc02, hc23, hlam, hphi, p2902_1]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h0, h1, h2682, h2888, hc12, hc23, hlam, hphi, p2902_1]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h0, h1, h2682, h2843, h2888, hc12, hc23, hlam, hphi, p2902_1]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h2678, hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h0, h2843, h2899, hc12, hlam, hphi, ht23, ht34, ht45, p2902_1, u5elo2]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h2841, hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h2843, hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h2679, hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p2902_1, u5elo0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [h2842, hlam, p2902_0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [hc04, hlam, hphi, ht45, p2902_1, u5elo0]
                                      · have p2902_0 := h2902c.1
                                        have p2902_1 := h2902c.2.1
                                        have p2902_2 := h2902c.2.2.1
                                        have p2902_3 := h2902c.2.2.2
                                        linarith only [hlam, p2902_0]
                                  · linarith only [h0, h2682, h2899, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                · linarith only [h1, h2788, h2842, h2888, h2898, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                              · linarith only [h1, h2679, h2888, h2890, h2895, h2897, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1, h2894, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1, h2842, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h1, h2678, h2841, hlam]
      · linarith only [h0, h2679, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2935 | h2935
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2936 | h2936
        · linarith only [h0, h1, h2936, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2938 | h2938
          · linarith only [h0, h2678, h2938, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2940 | h2940
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2941 | h2941
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2942 | h2942
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2943 | h2943
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2944 | h2944
                    · linarith only [h0, h1, h2936, h2944, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2946 | h2946
                      · linarith only [h0, h2678, h2938, h2946, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2948 | h2948
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2949 | h2949
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2950 | h2950
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2951 | h2951
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2952 | h2952
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2953 | h2953
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2954 | h2954
                                    · rcases h0bigk with h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [hlam, p2955_0]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h2678, h2944, h2949, hc02, hc23, hlam, hphi, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h1, hlam, p2955_0]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h2678, hlam, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h2678, h2944, h2949, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h0, hlam, p2955_0]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [hlam, p2955_0]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h2936, hlam, p2955_0]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h2938, hlam, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h0, h2678, h2935, h2944, h2949, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h1, h2944, hc02, hc23, hlam, hphi, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [hlam, p2955_0]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h0, h1, h2678, h2944, hc12, hc23, hlam, hphi, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        rcases p2955_3 (m.d 0 1) (by simp) with h2970 | h2970
                                        · linarith only [h1, h2970, hlam]
                                        · linarith only [h2935, h2970, hlam]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h0, h2948, h2952, h2954, hc04, hc45, hlam, hphi, ht0b, ht5b, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h0, h2948, h2952, h2954, hc04, hc45, hlam, hphi, ht0b, ht5b, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h2941, hlam, p2955_0]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [hlam, p2955_0]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        rcases p2955_3 (m.d 0 1) (by simp) with h2977 | h2977
                                        · linarith only [h2678, h2977, hlam]
                                        · linarith only [h2935, h2977, hlam]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h2935, hlam, p2955_0]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h2940, hlam, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h2942, hlam, p2955_0]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [h2943, hlam, p2955_1]
                                      · have p2955_0 := h2955c.1
                                        have p2955_1 := h2955c.2.1
                                        have p2955_2 := h2955c.2.2.1
                                        have p2955_3 := h2955c.2.2.2
                                        linarith only [hlam, p2955_0]
                                    · linarith only [h0, h2678, h2944, h2948, h2949, h2953, h2954, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h2935, h2938, h2948, h2950, h2952, h2953, hc35, hlam, hphi, u5elo0]
                                · linarith only [h0, h1, h2944, h2948, h2952, hc25, hlam, hphi, u5elo3]
                              · linarith only [h0, h1, h2944, h2948, h2951, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h2678, h2948, h2950, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h0, h1, h2941, h2948, h2949, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h1, h2940, h2944, h2948, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h2678, h2943, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h2941, h2942, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2994 | h2994
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2995 | h2995
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2996 | h2996
                    · linarith only [h0, h1, h2941, h2996, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2998 | h2998
                      · linarith only [h0, h1, h2938, h2941, h2998, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3000 | h3000
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3001 | h3001
                          · linarith only [h0, h1, h2941, h2996, h3000, h3001, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h1, h3000, h3001, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h2678, h2940, h2998, h3000, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2678, h2940, h2995, hc25, hlam, hphi, u5elo4]
                · linarith only [h0, h1, h2994, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3007 | h3007
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3008 | h3008
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3009 | h3009
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3010 | h3010
                    · linarith only [h0, h2940, h3010, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3012 | h3012
                      · linarith only [h0, h2940, h3012, hc24, hlam, hphi, ht45, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3014 | h3014
                        · linarith only [h0, h2940, h3014, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3016 | h3016
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3017 | h3017
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3018 | h3018
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3019 | h3019
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3020 | h3020
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3021 | h3021
                                    · rcases h0bigk with h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c | h3022c
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [hlam, p3022_0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h2678, h3016, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h1, hlam, p3022_0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h2678, hlam, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h2678, h3016, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h0, hlam, p3022_0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [hlam, p3022_0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h2936, hlam, p3022_0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h2938, hlam, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h2940, hlam, p3022_0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h0, h1, h3010, hc12, hc23, hlam, hphi, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [hlam, p3022_0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h1, h2678, h2935, h3010, h3014, hc12, hc23, hlam, hphi, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h1, h2935, h3010, h3014, hc12, hc23, hlam, hphi, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h2935, h3014, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h0, h2938, h3018, hc12, hc23, hlam, hphi, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h3007, hlam, p3022_0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [hlam, p3022_0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h1, h2935, h3007, h3010, h3014, hc12, hc23, hlam, hphi, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h2935, hlam, p3022_0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p3022_1, u5elo0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h3008, hlam, p3022_0]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [h3009, hlam, p3022_1]
                                      · have p3022_0 := h3022c.1
                                        have p3022_1 := h3022c.2.1
                                        have p3022_2 := h3022c.2.2.1
                                        have p3022_3 := h3022c.2.2.2
                                        linarith only [hlam, p3022_0]
                                    · rcases h0bigk with h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [hlam, p3048_0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h0, h2678, h3012, h3018, hc12, hc23, hlam, hphi, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h1, hlam, p3048_0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h2678, hlam, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h2678, h3012, h3018, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h0, hlam, p3048_0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [hlam, p3048_0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h2936, hlam, p3048_0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h2938, hlam, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h2940, hlam, p3048_0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h2935, h3017, h3021, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h0, h2936, hc12, hc23, hlam, hphi, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [hlam, p3048_0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h2678, h2935, h2936, h3017, h3021, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h2935, h2936, h3017, h3021, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h2935, h3017, h3021, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h0, h2678, h3012, hc12, hc24, hlam, hphi, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h3007, hlam, p3048_0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [hlam, p3048_0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h2678, h2935, h3012, h3017, h3021, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h2935, hlam, p3048_0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p3048_1, u5elo0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h3008, hlam, p3048_0]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [h3009, hlam, p3048_1]
                                      · have p3048_0 := h3048c.1
                                        have p3048_1 := h3048c.2.1
                                        have p3048_2 := h3048c.2.2.1
                                        have p3048_3 := h3048c.2.2.2
                                        linarith only [hlam, p3048_0]
                                  · linarith only [h0, h2678, h2935, h2938, h3010, h3016, h3017, h3020, hc12, hc23, hlam, hphi]
                                · linarith only [h2678, h2935, h3010, h3016, h3017, h3019, hc45, hlam, hphi, u5elo3]
                              · linarith only [h2678, h2935, h3010, h3014, h3016, h3018, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h2678, h2935, h3014, h3017, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1, h3007, h3016, hlam]
                  · linarith only [h2678, h2935, h3009, hc15, hlam, hphi, u5elo4]
                · linarith only [h0, h2678, h3007, h3008, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3081 | h3081
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3082 | h3082
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3083 | h3083
                    · linarith only [h0, h1, h3007, h3083, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3085 | h3085
                      · linarith only [h0, h2940, h3085, hc24, hlam, hphi, ht45, u5elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3087 | h3087
                        · linarith only [h0, h2940, h3087, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3089 | h3089
                          · linarith only [h0, h1, h3007, h3083, h3089, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h2935, h3087, h3089, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h2935, h3007, h3082, hc15, hlam, hphi, u5elo4]
                · linarith only [h0, h1, h3081, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · linarith only [h0, h2935, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

end R2N4
