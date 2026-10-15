import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_40S12
import Jsp000404.R1LeavesN7_40S13
import Jsp000404.R1LeavesN7_40S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6854000 in
set_option maxHeartbeats 6854000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1838 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2521 | h2521
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2522 | h2522
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2523 | h2523
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2524 | h2524
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2525 | h2525
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2526 | h2526
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2527 | h2527
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2528 | h2528
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2529 | h2529
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2530 | h2530
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2531 | h2531
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2532 | h2532
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2533 | h2533
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2534 | h2534
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2535 | h2535
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2536 | h2536
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2537 | h2537
                                  · linarith only [h2522, h2534, h2537, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h1838, h2527, h2537, hc34, hlam, hphi, u4elo1]
                                · linarith only [h1838, h2521, h2533, h2536, hc24, hlam, hphi, u4elo1]
                              · linarith only [h1838, h2521, h2526, h2535, hc23, hlam, hphi, ht34, u4elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2542 | h2542
                              · linarith only [h2522, h2525, h2534, h2542, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h1838, h2521, h2526, h2542, hc23, hlam, hphi, ht34, u4elo1]
                          · linarith only [h1838, h2533, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1314, h2526, h2532, hlam]
                      · linarith only [h1314, h2525, h2531, hlam]
                    · linarith only [h0, h2524, h2530, hlam]
                  · linarith only [h0, h2522, h2525, h2529, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h2522, h2528, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1838, h2521, h2527, hlam]
            · linarith only [h1314, h2521, h2526, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2553 | h2553
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2554 | h2554
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2555 | h2555
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2556 | h2556
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2557 | h2557
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2558 | h2558
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2559 | h2559
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2560 | h2560
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2561 | h2561
                            · linarith only [h1838, h2521, h2522, h2525, h2557, h2561, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2563 | h2563
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2564 | h2564
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2565 | h2565
                                  · rcases h0bigk with h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [hlam, p2566_0]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h0, hlam, p2566_1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h1314, hlam, p2566_0]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h1838, hlam, p2566_1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h1314, h2525, h2555, h2558, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2566_1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2521, hc15, hlam, hphi, ht0b, ht5b, p2566_1, u0elo1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [hlam, p2566_0]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h1314, h2521, h2557, h2563, h2565, hc45, hlam, hphi, ht0b, ht5b, p2566_1, u0elo1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h1314, h2521, h2525, h2557, h2563, h2565, hc45, hlam, hphi, ht0b, ht5b, p2566_1, u0elo1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      rcases p2566_3 (m.d 0 1) (by simp) with h2576 | h2576
                                      · linarith only [h0, h2576, hlam]
                                      · linarith only [h2521, h2576, hlam]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2521, h2525, h2557, h2558, h2563, h2565, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2566_1, u4elo1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2522, hlam, p2566_1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [hlam, p2566_0]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2525, hlam, p2566_1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2521, h2525, h2557, h2558, h2563, h2565, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2566_1, u4elo1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2521, h2557, h2563, h2565, hc45, hlam, hphi, ht0b, ht5b, p2566_1, u0elo3]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2523, hlam, p2566_0]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2525, h2558, hc03, hlam, hphi, ht34, p2566_1, u4elo1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [hlam, p2566_0]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      rcases p2566_3 (m.d 0 1) (by simp) with h2588 | h2588
                                      · linarith only [h1838, h2588, hlam]
                                      · linarith only [h2521, h2588, hlam]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2521, hlam, p2566_0]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2524, hlam, p2566_1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2553, hlam, p2566_0]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [h2554, hlam, p2566_1]
                                    · have p2566_0 := h2566c.1
                                      have p2566_1 := h2566c.2.1
                                      have p2566_2 := h2566c.2.2.1
                                      have p2566_3 := h2566c.2.2.2
                                      linarith only [hlam, p2566_0]
                                  · linarith only [h1314, h2521, h2525, h2557, h2563, h2565, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                                · linarith only [h1314, h2521, h2525, h2558, h2560, h2564, hc24, hlam, hphi, u4elo1]
                              · linarith only [h2525, h2553, h2558, h2563, hc23, hlam, hphi, ht34, u4elo1]
                          · linarith only [h1314, h2521, h2525, h2557, h2558, h2560, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h1314, h2521, h2525, h2557, h2558, h2559, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1314, h2521, h2557, h2558, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h0, h2524, h2557, hlam]
                  · linarith only [h0, h2521, h2556, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                · linarith only [h0, h2522, h2555, hlam]
              · linarith only [h1314, h2521, h2525, h2554, hlam]
            · linarith only [h1314, h2521, h2553, hlam]
        · linarith only [h0, h2521, h2524, hlam]
      · linarith only [h2522, h2523, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2609 | h2609
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2610 | h2610
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2611 | h2611
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2612 | h2612
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2613 | h2613
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2614 | h2614
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2615 | h2615
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2616 | h2616
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2617 | h2617
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2618 | h2618
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2619 | h2619
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2620 | h2620
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2621 | h2621
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2622 | h2622
                                · linarith only [h2522, h2609, h2614, h2622, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h2522, h2609, h2613, h2614, h2622, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h1838, h2521, h2522, h2612, h2616, h2621, hc02, hc25, hlam, hphi, ht0b, ht23, ht34, ht5b, u0elo2, u4elo1]
                            · linarith only [h1838, h2521, h2522, h2609, h2616, h2620, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h1838, h2521, h2616, h2619, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h2522, h2609, h2612, h2614, h2618, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1314, h2521, h2609, h2611, h2616, h2617, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h2522, h2610, h2616, hc12, hc23, hlam, hphi]
                  · linarith only [h2522, h2609, h2614, h2615, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2632 | h2632
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2633 | h2633
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2634 | h2634
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2635 | h2635
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2636 | h2636
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2637 | h2637
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2638 | h2638
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2639 | h2639
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2640 | h2640
                                  · rcases h0bigk with h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [hlam, p2641_0]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h0, hlam, p2641_1]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h1314, hlam, p2641_0]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h1838, hlam, p2641_1]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h1838, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2641_1, u4elo1]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h0, h2614, hc01, hc23, hlam, hphi, ht12, p2641_1]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [hlam, p2641_0]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h2522, hlam, p2641_0]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h0, h1838, h2521, h2614, h2633, h2638, h2640, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2641_1]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      rcases p2641_3 (m.d 0 1) (by simp) with h2651 | h2651
                                      · linarith only [h0, h2651, hlam]
                                      · linarith only [h2521, h2651, hlam]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h2521, h2633, h2638, h2640, hc45, hlam, hphi, ht0b, ht5b, p2641_1, u0elo2]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h0, h2521, h2633, h2638, h2640, hc45, hlam, hphi, ht0b, ht5b, p2641_1, u0elo2]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [hlam, p2641_0]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h1838, h2521, h2633, h2638, h2640, hc45, hlam, hphi, ht0b, ht5b, p2641_1, u0elo2]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      rcases p2641_3 (m.d 0 1) (by simp) with h2658 | h2658
                                      · linarith only [h1314, h2658, hlam]
                                      · linarith only [h2521, h2658, hlam]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h2521, h2633, h2638, h2640, hc45, hlam, hphi, ht0b, ht5b, p2641_1, u0elo3]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h2609, hlam, p2641_0]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h2611, hlam, p2641_0]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [hlam, p2641_0]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      rcases p2641_3 (m.d 0 1) (by simp) with h2665 | h2665
                                      · linarith only [h1838, h2665, hlam]
                                      · linarith only [h2521, h2665, hlam]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h2521, hlam, p2641_0]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h2610, hlam, p2641_1]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h2612, hlam, p2641_0]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [h2613, hlam, p2641_1]
                                    · have p2641_0 := h2641c.1
                                      have p2641_1 := h2641c.2.1
                                      have p2641_2 := h2641c.2.2.1
                                      have p2641_3 := h2641c.2.2.2
                                      linarith only [hlam, p2641_0]
                                  · linarith only [h2613, h2640, hc34, hlam, hphi, u4elo0]
                                · linarith only [h1838, h2521, h2636, h2639, hc24, hlam, hphi, u4elo1]
                              · linarith only [h0, h2521, h2614, h2633, h2638, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1838, h2521, h2614, h2632, h2633, h2637, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1838, h2521, h2633, h2636, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h1314, h2612, h2635, hlam]
                      · linarith only [h1314, h2611, h2634, hlam]
                    · linarith only [h0, h2610, h2633, hlam]
                  · linarith only [h0, h2521, h2632, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h1838, h2521, h2613, hlam]
            · linarith only [h1314, h2521, h2612, hlam]
          · linarith only [h2522, h2609, h2611, hc24, hlam, hphi, u4elo3]
        · linarith only [h1838, h2521, h2609, h2610, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2686 | h2686
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2687 | h2687
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2688 | h2688
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2689 | h2689
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2690 | h2690
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2691 | h2691
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2692 | h2692
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2693 | h2693
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2694 | h2694
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2695 | h2695
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2696 | h2696
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2697 | h2697
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2698 | h2698
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2699 | h2699
                                  · rcases h0bigk with h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [hlam, p2700_0]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h0, hlam, p2700_1]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h1314, hlam, p2700_0]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h1838, hlam, p2700_1]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h0, h2609, h2690, h2696, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2700_1]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h2609, h2690, h2696, hc01, hc12, hlam, hphi, p2700_1]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [hlam, p2700_0]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h2522, hlam, p2700_0]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h2609, hlam, p2700_1]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h2521, h2609, h2692, h2697, h2699, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2700_1, u4elo2]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h2521, h2692, h2697, h2699, hc45, hlam, hphi, ht0b, ht5b, p2700_1, u0elo2]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h0, h2521, h2692, h2697, h2699, hc45, hlam, hphi, ht0b, ht5b, p2700_1, u0elo2]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [hlam, p2700_0]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h0, h2521, h2522, h2609, h2690, h2692, h2697, h2699, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2700_1]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      rcases p2700_3 (m.d 0 1) (by simp) with h2715 | h2715
                                      · linarith only [h1314, h2715, hlam]
                                      · linarith only [h2521, h2715, hlam]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h2521, h2692, h2697, h2699, hc45, hlam, hphi, ht0b, ht5b, p2700_1, u0elo3]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h0, h2521, h2609, h2691, h2692, h2697, h2699, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2700_1, u4elo1]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h2687, hlam, p2700_0]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [hlam, p2700_0]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      rcases p2700_3 (m.d 0 1) (by simp) with h2722 | h2722
                                      · linarith only [h1838, h2722, hlam]
                                      · linarith only [h2521, h2722, hlam]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h2521, hlam, p2700_0]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h2686, hlam, p2700_1]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h2688, hlam, p2700_0]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [h2689, hlam, p2700_1]
                                    · have p2700_0 := h2700c.1
                                      have p2700_1 := h2700c.2.1
                                      have p2700_2 := h2700c.2.2.1
                                      have p2700_3 := h2700c.2.2.2
                                      linarith only [hlam, p2700_0]
                                  · linarith only [h2609, h2689, h2691, h2699, hc34, hlam, hphi, u4elo1]
                                · linarith only [h1838, h2521, h2609, h2695, h2698, hc04, hlam, hphi, u4elo1]
                              · linarith only [h2522, h2688, h2697, hlam]
                            · linarith only [h0, h2521, h2522, h2695, h2696, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h0, h2521, h2609, h2691, h2692, h2695, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h1314, h2521, h2688, h2692, h2694, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h1314, h2521, h2692, h2693, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h2522, h2686, h2692, hc12, hc23, hlam, hphi]
                  · linarith only [h2522, h2690, h2691, hc03, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2739 | h2739
                  · linarith only [h0, h2609, h2690, h2739, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2521, h2739, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h0, h2521, h2609, h2689, hlam]
            · linarith only [h1314, h2521, h2688, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2744 | h2744
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2745 | h2745
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2746 | h2746
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2747 | h2747
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2748 | h2748
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2749 | h2749
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2750 | h2750
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2751 | h2751
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2752 | h2752
                            · linarith only [h0, h2522, h2687, h2746, h2752, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h2521, h2522, h2748, h2749, h2752, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                          · linarith only [h1838, h2521, h2748, h2751, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h0, h2521, h2522, h2687, h2748, h2749, h2750, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1314, h2521, h2748, h2749, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h2522, h2686, h2748, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h2522, h2746, h2747, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2760 | h2760
                  · linarith only [h0, h2521, h2609, h2746, h2760, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h2521, h2760, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h1314, h2521, h2687, h2745, hlam]
            · linarith only [h0, h2521, h2522, h2744, hlam]
        · linarith only [h0, h2521, h2686, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2766 | h2766
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2767 | h2767
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2768 | h2768
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2769 | h2769
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2770 | h2770
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2771 | h2771
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2772 | h2772
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2773 | h2773
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2774 | h2774
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2775 | h2775
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2776 | h2776
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2777 | h2777
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2778 | h2778
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2779 | h2779
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2780 | h2780
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2781 | h2781
                                  · linarith only [h2766, h2778, h2781, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h2771, h2781, hc34, hlam, hphi, u4elo0]
                                · linarith only [h2771, h2780, hc24, hlam, hphi, u4elo0]
                              · linarith only [h2521, h2770, h2777, h2778, h2779, hc34, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2786 | h2786
                              · linarith only [h2766, h2769, h2778, h2786, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2788 | h2788
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2789 | h2789
                                  · rcases h0bigk with h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [hlam, p2790_0]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h0, hlam, p2790_1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h1314, hlam, p2790_0]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h1838, hlam, p2790_1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2521, hlam, p2790_1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      rcases p2790_3 (m.d 0 1) (by simp) with h2796 | h2796
                                      · linarith only [h0, h2796, hlam]
                                      · rcases p2790_3 (m.d 0 2) (by simp) with h2798 | h2798
                                        · rcases p2790_3 (m.d 0 3) (by simp) with h2799 | h2799
                                          · linarith only [h2766, h2799, hlam]
                                          · linarith only [h1314, h2799, hlam]
                                        · linarith only [h0, h2798, hlam]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [hlam, p2790_0]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2769, h2786, h2789, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2790_1, u0elo1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2767, h2788, hc45, hlam, hphi, ht0b, ht5b, p2790_1, u0elo1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2770, h2786, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2790_1, u0elo1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      rcases p2790_3 (m.d 0 1) (by simp) with h2807 | h2807
                                      · linarith only [h1314, h2807, hlam]
                                      · rcases p2790_3 (m.d 0 2) (by simp) with h2809 | h2809
                                        · rcases p2790_3 (m.d 0 3) (by simp) with h2810 | h2810
                                          · rcases p2790_3 (m.d 0 4) (by simp) with h2811 | h2811
                                            · linarith only [h2769, h2811, hlam]
                                            · linarith only [h1838, h2811, hlam]
                                          · linarith only [h1314, h2810, hlam]
                                        · linarith only [h0, h2809, hlam]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2766, hlam, p2790_1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [hlam, p2790_0]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2769, h2786, h2789, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2790_1, u0elo2]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2766, h2770, h2786, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2790_1, u0elo1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2790_1, u4elo0]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2767, hlam, p2790_0]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2769, hlam, p2790_0]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [hlam, p2790_0]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h1838, h2770, h2786, hc23, hlam, hphi, ht34, p2790_1, u4elo1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2521, h2777, hc01, hlam, hphi, ht12, ht23, ht34, p2790_1, u4elo1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2768, hlam, p2790_1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2770, hlam, p2790_0]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [h2771, hlam, p2790_1]
                                    · have p2790_0 := h2790c.1
                                      have p2790_1 := h2790c.2.1
                                      have p2790_2 := h2790c.2.2.1
                                      have p2790_3 := h2790c.2.2.2
                                      linarith only [hlam, p2790_0]
                                  · linarith only [h2788, h2789, hc34, hlam, hphi, u4elo2]
                                · linarith only [h1838, h2771, h2788, hc24, hlam, hphi, u4elo1]
                          · linarith only [h1838, h2771, h2777, hlam]
                        · linarith only [h1314, h2770, h2776, hlam]
                      · linarith only [h1314, h2769, h2775, hlam]
                    · linarith only [h0, h2768, h2774, hlam]
                  · linarith only [h0, h2766, h2769, h2773, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h2766, h2772, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2838 | h2838
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2839 | h2839
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2840 | h2840
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2841 | h2841
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2842 | h2842
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2843 | h2843
                          · linarith only [h2771, h2843, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h2843, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1314, h2766, h2770, h2842, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1314, h2769, h2771, h2841, hc03, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h2768, h2840, hlam]
                  · linarith only [h0, h2767, h2771, h2839, hc02, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h0, h2766, h2838, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2851 | h2851
              · linarith only [h2769, h2770, h2851, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2853 | h2853
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2854 | h2854
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2855 | h2855
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2856 | h2856
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2857 | h2857
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2858 | h2858
                          · linarith only [h2851, h2858, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h2858, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2861 | h2861
                          · linarith only [h2851, h2861, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h2861, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h1314, h2768, h2769, h2770, h2856, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h2768, h2855, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2767, h2854, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                · linarith only [h0, h2766, h2853, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2868 | h2868
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2869 | h2869
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2870 | h2870
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2871 | h2871
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2872 | h2872
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2873 | h2873
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2874 | h2874
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2875 | h2875
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2876 | h2876
                            · linarith only [h2766, h2769, h2868, h2876, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2878 | h2878
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2879 | h2879
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2880 | h2880
                                  · rcases h0bigk with h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c | h2881c
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [hlam, p2881_0]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h0, hlam, p2881_1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h1314, hlam, p2881_0]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h1838, hlam, p2881_1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2521, hlam, p2881_1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      rcases p2881_3 (m.d 0 1) (by simp) with h2887 | h2887
                                      · linarith only [h0, h2887, hlam]
                                      · rcases p2881_3 (m.d 0 2) (by simp) with h2889 | h2889
                                        · rcases p2881_3 (m.d 0 3) (by simp) with h2890 | h2890
                                          · linarith only [h2766, h2890, hlam]
                                          · linarith only [h1314, h2890, hlam]
                                        · linarith only [h0, h2889, hlam]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [hlam, p2881_0]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2766, h2878, h2880, hc45, hlam, hphi, ht0b, ht5b, p2881_1, u0elo1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2766, h2769, h2878, h2880, hc45, hlam, hphi, ht0b, ht5b, p2881_1, u0elo1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      rcases p2881_3 (m.d 0 1) (by simp) with h2897 | h2897
                                      · linarith only [h0, h2897, hlam]
                                      · rcases p2881_3 (m.d 0 2) (by simp) with h2899 | h2899
                                        · rcases p2881_3 (m.d 0 3) (by simp) with h2900 | h2900
                                          · linarith only [h2766, h2900, hlam]
                                          · linarith only [h2868, h2900, hlam]
                                        · linarith only [h2768, h2899, hlam]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2769, h2870, h2873, hc01, hc12, hlam, hphi, p2881_1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2766, hlam, p2881_1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [hlam, p2881_0]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2769, hlam, p2881_1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2769, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2881_1, u4elo3]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2881_1, u4elo0]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2767, hlam, p2881_0]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h1838, hc03, hlam, hphi, ht34, p2881_1, u4elo1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [hlam, p2881_0]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h1838, h2521, hc01, hlam, hphi, ht12, ht23, ht34, p2881_1, u4elo1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2521, h2875, hc01, hlam, hphi, ht12, ht23, ht34, p2881_1, u4elo1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2768, hlam, p2881_1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2868, hlam, p2881_0]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [h2869, hlam, p2881_1]
                                    · have p2881_0 := h2881c.1
                                      have p2881_1 := h2881c.2.1
                                      have p2881_2 := h2881c.2.2.1
                                      have p2881_3 := h2881c.2.2.2
                                      linarith only [hlam, p2881_0]
                                  · linarith only [h2766, h2769, h2878, h2880, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                                · linarith only [h2769, h2868, h2869, h2879, hc24, hlam, hphi, u4elo3]
                              · linarith only [h2769, h2868, h2873, h2878, hc23, hlam, hphi, ht34, u4elo1]
                          · linarith only [h2769, h2868, h2869, h2873, h2875, hlam]
                        · linarith only [h2769, h2868, h2873, h2874, hc13, hlam, hphi, ht34, u4elo1]
                      · linarith only [h1314, h2873, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2768, h2872, hlam]
                  · linarith only [h0, h2871, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2766, h2870, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h2769, h2868, h2869, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2929 | h2929
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2930 | h2930
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2931 | h2931
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2932 | h2932
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2933 | h2933
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2934 | h2934
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2935 | h2935
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2936 | h2936
                            · linarith only [h1314, h2766, h2769, h2936, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2938 | h2938
                              · linarith only [h2766, h2868, h2938, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2940 | h2940
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2941 | h2941
                                  · rcases h0bigk with h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c | h2942c
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [hlam, p2942_0]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h0, hlam, p2942_1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h1314, hlam, p2942_0]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h1838, hlam, p2942_1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h2521, hlam, p2942_1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      rcases p2942_3 (m.d 0 1) (by simp) with h2948 | h2948
                                      · linarith only [h0, h2948, hlam]
                                      · rcases p2942_3 (m.d 0 2) (by simp) with h2950 | h2950
                                        · rcases p2942_3 (m.d 0 3) (by simp) with h2951 | h2951
                                          · linarith only [h2766, h2951, hlam]
                                          · linarith only [h1314, h2951, hlam]
                                        · linarith only [h0, h2950, hlam]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [hlam, p2942_0]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      rcases p2942_3 (m.d 0 1) (by simp) with h2956 | h2956
                                      · linarith only [h0, h2956, hlam]
                                      · rcases p2942_3 (m.d 0 2) (by simp) with h2958 | h2958
                                        · rcases p2942_3 (m.d 0 3) (by simp) with h2959 | h2959
                                          · linarith only [h2766, h2959, hlam]
                                          · rcases p2942_3 (m.d 0 4) (by simp) with h2961 | h2961
                                            · linarith only [h2767, h2961, hlam]
                                            · linarith only [h2769, h2961, hlam]
                                        · linarith only [h2766, h2958, hlam]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h2767, h2940, hc45, hlam, hphi, ht0b, ht5b, p2942_1, u0elo1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      rcases p2942_3 (m.d 0 1) (by simp) with h2966 | h2966
                                      · linarith only [h0, h2966, hlam]
                                      · rcases p2942_3 (m.d 0 2) (by simp) with h2968 | h2968
                                        · rcases p2942_3 (m.d 0 3) (by simp) with h2969 | h2969
                                          · linarith only [h2766, h2969, hlam]
                                          · rcases p2942_3 (m.d 0 4) (by simp) with h2971 | h2971
                                            · linarith only [h2767, h2971, hlam]
                                            · linarith only [h2929, h2971, hlam]
                                        · linarith only [h2768, h2968, hlam]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h2868, h2933, h2941, hc01, hc13, hlam, hphi, p2942_1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h2766, hlam, p2942_1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [hlam, p2942_0]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h2769, hlam, p2942_1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h2868, hlam, p2942_1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2942_1, u4elo0]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h2767, hlam, p2942_0]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h1838, hc03, hlam, hphi, ht34, p2942_1, u4elo1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [hlam, p2942_0]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h1838, h2521, hc01, hlam, hphi, ht12, ht23, ht34, p2942_1, u4elo1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h2868, h2941, hc01, hlam, hphi, ht12, ht23, ht34, p2942_1, u4elo3]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h2768, hlam, p2942_1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h1314, h2868, h2941, hc01, hlam, hphi, ht12, ht23, ht34, p2942_1, u4elo3]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [h2929, hlam, p2942_1]
                                    · have p2942_0 := h2942c.1
                                      have p2942_1 := h2942c.2.1
                                      have p2942_2 := h2942c.2.2.1
                                      have p2942_3 := h2942c.2.2.2
                                      linarith only [hlam, p2942_0]
                                  · linarith only [h2769, h2940, h2941, hc04, hlam, hphi, u4elo2]
                                · linarith only [h2929, h2940, hc24, hlam, hphi, u4elo0]
                          · linarith only [h2769, h2929, h2933, h2935, hlam]
                        · linarith only [h1314, h2769, h2933, h2934, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1314, h2933, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2768, h2932, hlam]
                  · linarith only [h0, h2931, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2766, h2930, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2998 | h2998
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2999 | h2999
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3000 | h3000
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3001 | h3001
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3002 | h3002
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3003 | h3003
                          · linarith only [h2929, h3003, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h3003, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1314, h2769, h3001, h3002, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1314, h3001, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2768, h3000, hlam]
                  · linarith only [h0, h2999, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2766, h2998, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3011 | h3011
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3012 | h3012
            · linarith only [h2766, h2768, h3012, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3014 | h3014
              · linarith only [h2766, h2768, h3011, h3014, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3016 | h3016
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3017 | h3017
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3018 | h3018
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3019 | h3019
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3020 | h3020
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3021 | h3021
                          · linarith only [h3014, h3021, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h3021, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3024 | h3024
                          · linarith only [h1838, h3014, h3024, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h1838, h3024, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h1314, h3019, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3028 | h3028
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3029 | h3029
                        · linarith only [h3011, h3012, h3016, h3018, h3029, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3031 | h3031
                          · linarith only [h1838, h3014, h3031, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h1838, h3031, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h0, h1314, h2766, h3011, h3018, h3028, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2766, h3017, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h0, h2766, h3016, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3037 | h3037
            · linarith only [h2766, h2768, h3037, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3039 | h3039
              · linarith only [h2767, h2768, h3039, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3041 | h3041
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3042 | h3042
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3043 | h3043
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3044 | h3044
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3045 | h3045
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3046 | h3046
                          · linarith only [h1314, h3011, h3039, h3046, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h1838, h3046, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1314, h3011, h3044, h3045, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1314, h3044, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3051 | h3051
                      · linarith only [h1314, h3011, h3041, h3043, h3051, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h1314, h3051, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h2767, h3042, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h2766, h3041, hlam]
      · linarith only [h2766, h2767, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3057 | h3057
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3058 | h3058
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3059 | h3059
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3060 | h3060
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3061 | h3061
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3062 | h3062
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3063 | h3063
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3064 | h3064
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3065 | h3065
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3066 | h3066
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3067 | h3067
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3068 | h3068
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3069 | h3069
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3070 | h3070
                                · linarith only [h2766, h3057, h3062, h3070, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h3061, h3068, h3070, hc34, hlam, hphi, u4elo0]
                              · linarith only [h2766, h3060, h3069, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h2766, h3057, h3068, hc24, hlam, hphi, u4elo3]
                          · linarith only [h3061, h3067, hc14, hlam, hphi, u4elo0]
                        · linarith only [h2766, h3057, h3060, h3062, h3066, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1314, h3059, h3065, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                    · linarith only [h2766, h3062, h3064, hc02, hc25, hlam, hphi]
                  · linarith only [h2766, h3057, h3061, h3062, h3063, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3080 | h3080
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3081 | h3081
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3082 | h3082
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3083 | h3083
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3084 | h3084
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3085 | h3085
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3086 | h3086
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3087 | h3087
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3088 | h3088
                                  · rcases h0bigk with h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c | h3089c
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [hlam, p3089_0]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h0, hlam, p3089_1]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h1314, hlam, p3089_0]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h1838, hlam, p3089_1]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h2521, hlam, p3089_1]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h0, h3062, hc01, hc23, hlam, hphi, ht12, p3089_1]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [hlam, p3089_0]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h2766, hlam, p3089_0]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h0, h3057, h3062, h3085, h3088, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3089_1]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h0, h2521, h3062, hc01, hc23, hlam, hphi, ht12, p3089_1]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      rcases p3089_3 (m.d 0 1) (by simp) with h3100 | h3100
                                      · linarith only [h1314, h3100, hlam]
                                      · rcases p3089_3 (m.d 0 2) (by simp) with h3102 | h3102
                                        · linarith only [h2766, h3102, hlam]
                                        · linarith only [h0, h3102, hlam]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h3057, h3085, h3088, hc45, hlam, hphi, ht0b, ht5b, p3089_1, u0elo2]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [hlam, p3089_0]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h3057, h3085, h3088, hc45, hlam, hphi, ht0b, ht5b, p3089_1, u0elo2]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      rcases p3089_3 (m.d 0 1) (by simp) with h3108 | h3108
                                      · linarith only [h1314, h3108, hlam]
                                      · rcases p3089_3 (m.d 0 2) (by simp) with h3110 | h3110
                                        · linarith only [h2766, h3110, hlam]
                                        · linarith only [h3058, h3110, hlam]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p3089_1, u4elo0]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h3057, hlam, p3089_0]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h3059, hlam, p3089_0]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [hlam, p3089_0]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h1838, h2521, hc01, hlam, hphi, ht12, ht23, ht34, p3089_1, u4elo1]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h2521, h3084, hc01, hlam, hphi, ht12, ht23, ht34, p3089_1, u4elo1]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h3058, hlam, p3089_1]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h3060, hlam, p3089_0]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [h3061, hlam, p3089_1]
                                    · have p3089_0 := h3089c.1
                                      have p3089_1 := h3089c.2.1
                                      have p3089_2 := h3089c.2.2.1
                                      have p3089_3 := h3089c.2.2.2
                                      linarith only [hlam, p3089_0]
                                  · linarith only [h1838, h3061, h3088, hc34, hlam, hphi, u4elo1]
                                · linarith only [h1838, h3061, h3087, hc24, hlam, hphi, u4elo1]
                              · linarith only [h0, h3062, h3086, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h1314, h3062, h3085, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h1838, h3061, h3084, hlam]
                        · linarith only [h1314, h2766, h3058, h3060, h3083, hlam]
                      · linarith only [h1314, h3059, h3082, hlam]
                    · linarith only [h0, h3058, h3081, hlam]
                  · linarith only [h0, h3080, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3132 | h3132
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3133 | h3133
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3134 | h3134
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3135 | h3135
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3136 | h3136
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3137 | h3137
                          · linarith only [h3061, h3137, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h3137, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h2766, h3058, h3060, h3132, h3136, hlam]
                      · linarith only [h2766, h3057, h3132, h3135, hc24, hlam, hphi, u4elo3]
                    · linarith only [h2766, h3058, h3134, hc12, hc23, hlam, hphi]
                  · linarith only [h2766, h3132, h3133, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3144 | h3144
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3145 | h3145
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3146 | h3146
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3147 | h3147
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3148 | h3148
                          · linarith only [h1838, h3061, h3132, h3144, h3148, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h1838, h3148, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h1314, h3058, h3060, h3132, h3147, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h1314, h3059, h3146, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                    · linarith only [h0, h3058, h3145, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h3144, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h2766, h3058, h3060, hlam]
          · linarith only [h2766, h3057, h3059, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3157 | h3157
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3158 | h3158
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3159 | h3159
              · linarith only [h3057, h3058, h3159, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3161 | h3161
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3162 | h3162
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3163 | h3163
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3164 | h3164
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3165 | h3165
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3166 | h3166
                          · linarith only [h3159, h3166, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h3166, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1314, h3158, h3165, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1314, h3157, h3164, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                    · linarith only [h2766, h3057, h3161, h3163, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h2766, h3057, h3161, h3162, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3173 | h3173
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3174 | h3174
                    · linarith only [h3057, h3058, h3161, h3174, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3176 | h3176
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3177 | h3177
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3178 | h3178
                          · linarith only [h3159, h3178, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h3178, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1314, h3158, h3177, hlam]
                      · linarith only [h1838, h3161, h3173, h3176, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h3057, h3173, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3184 | h3184
              · linarith only [h2766, h3057, h3158, h3184, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3186 | h3186
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3187 | h3187
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3188 | h3188
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3189 | h3189
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3190 | h3190
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3191 | h3191
                          · linarith only [h3184, h3191, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h3191, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3194 | h3194
                          · linarith only [h3157, h3158, h3184, h3194, hc34, hlam, hphi, u4elo1]
                          · linarith only [h1838, h3194, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h2766, h3057, h3186, h3189, hc24, hlam, hphi, u4elo3]
                    · linarith only [h2766, h3057, h3186, h3188, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h2766, h3057, h3186, h3187, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3200 | h3200
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3201 | h3201
                    · linarith only [h3057, h3058, h3186, h3201, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3203 | h3203
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3204 | h3204
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3205 | h3205
                          · linarith only [h3184, h3205, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h3205, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3208 | h3208
                          · linarith only [h1838, h3184, h3208, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h1838, h3208, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h0, h3157, h3186, h3203, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h3057, h3200, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h2766, h3057, h3157, hc24, hlam, hphi, u4elo3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3214 | h3214
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3215 | h3215
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3216 | h3216
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3217 | h3217
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3218 | h3218
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3219 | h3219
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3220 | h3220
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3221 | h3221
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3222 | h3222
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3223 | h3223
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3224 | h3224
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3225 | h3225
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3226 | h3226
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3227 | h3227
                                  · rcases h0bigk with h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c | h3228c
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [hlam, p3228_0]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h0, hlam, p3228_1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h1314, hlam, p3228_0]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h1838, hlam, p3228_1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h2521, hlam, p3228_1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h3057, h3219, h3221, hc01, hc13, hlam, hphi, p3228_1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [hlam, p3228_0]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h2766, hlam, p3228_0]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h3057, hlam, p3228_1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h1838, h2521, h3057, hc01, hlam, hphi, ht12, ht23, ht34, p3228_1, u4elo1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h2766, h3218, hc01, hc12, hlam, hphi, p3228_1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h3214, hc25, hlam, hphi, ht0b, ht5b, p3228_1, u0elo2]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [hlam, p3228_0]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h3057, h3214, h3225, hc35, hlam, hphi, ht0b, ht5b, p3228_1, u0elo2]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h2521, h2766, h3218, hc01, hc12, hlam, hphi, p3228_1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p3228_1, u4elo0]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h1838, h3214, h3225, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3228_1, u4elo1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h3215, hlam, p3228_0]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [hlam, p3228_0]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h1838, h2521, hc01, hlam, hphi, ht12, ht23, ht34, p3228_1, u4elo1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h2766, h3214, h3218, hc01, hc12, hlam, hphi, p3228_1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h3214, hlam, p3228_1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h3216, hlam, p3228_0]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [h3217, hlam, p3228_1]
                                    · have p3228_0 := h3228c.1
                                      have p3228_1 := h3228c.2.1
                                      have p3228_2 := h3228c.2.2.1
                                      have p3228_3 := h3228c.2.2.2
                                      linarith only [hlam, p3228_0]
                                  · linarith only [h3057, h3217, h3219, h3227, hc34, hlam, hphi, u4elo1]
                                · linarith only [h3057, h3214, h3217, h3226, hlam]
                              · linarith only [h2766, h3216, h3225, hlam]
                            · linarith only [h2766, h3224, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h1838, h3223, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h3057, h3214, h3216, h3219, h3222, hc13, hlam, hphi, ht34, u4elo1]
                      · linarith only [h1314, h3221, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h2766, h3214, h3220, hc12, hc23, hlam, hphi]
                  · linarith only [h2766, h3218, h3219, hc03, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3263 | h3263
                  · linarith only [h2521, h3057, h3214, h3218, h3263, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3263, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h3057, h3214, h3217, hlam]
            · linarith only [h3057, h3214, h3215, h3216, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3268 | h3268
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3269 | h3269
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3270 | h3270
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3271 | h3271
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3272 | h3272
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3273 | h3273
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3274 | h3274
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3275 | h3275
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3276 | h3276
                            · linarith only [h2766, h3214, h3215, h3270, h3276, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h2766, h3214, h3273, h3276, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                          · linarith only [h3269, h3275, hc14, hlam, hphi, u4elo0]
                        · linarith only [h3215, h3268, h3273, h3274, hlam]
                      · linarith only [h1314, h3273, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h2766, h3214, h3272, hc12, hc23, hlam, hphi]
                  · linarith only [h2766, h3270, h3271, hc02, hlam, hphi, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3284 | h3284
                  · linarith only [h3057, h3214, h3270, h3284, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h3284, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h2766, h3214, h3215, h3269, hlam]
            · linarith only [h2766, h3214, h3268, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3289 | h3289
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3290 | h3290
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3291 | h3291
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3292 | h3292
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3293 | h3293
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3294 | h3294
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3295 | h3295
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3296 | h3296
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3297 | h3297
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3298 | h3298
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3299 | h3299
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3300 | h3300
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3301 | h3301
                                  · rcases h0bigk with h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c | h3302c
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [hlam, p3302_0]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h0, hlam, p3302_1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h1314, hlam, p3302_0]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h1838, hlam, p3302_1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h2521, hlam, p3302_1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h3214, h3294, hc01, hc15, hlam, hphi, p3302_1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [hlam, p3302_0]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h2766, hlam, p3302_0]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h3057, hlam, p3302_1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h3214, hlam, p3302_0]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h2766, h3292, hc01, hc12, hlam, hphi, p3302_1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h0, h2766, h3292, hc01, hc12, hlam, hphi, p3302_1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [hlam, p3302_0]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h3289, h3301, hc45, hlam, hphi, ht0b, ht5b, p3302_1, u0elo2]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h0, h2766, h3214, h3292, hc01, hc12, hlam, hphi, p3302_1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p3302_1, u4elo0]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h0, h3057, h3293, hc01, hlam, hphi, ht12, ht23, ht34, p3302_1, u4elo1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h3289, hlam, p3302_0]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [hlam, p3302_0]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h0, h3057, h3214, h3293, hc01, hlam, hphi, ht12, ht23, ht34, p3302_1, u4elo1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h3057, h3291, h3293, hc01, hlam, hphi, ht12, ht23, ht34, p3302_1, u4elo1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h0, h3057, h3291, h3293, hc01, hlam, hphi, ht12, ht23, ht34, p3302_1, u4elo1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h3290, hlam, p3302_0]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [h3291, hlam, p3302_1]
                                    · have p3302_0 := h3302c.1
                                      have p3302_1 := h3302c.2.1
                                      have p3302_2 := h3302c.2.2.1
                                      have p3302_3 := h3302c.2.2.2
                                      linarith only [hlam, p3302_0]
                                  · linarith only [h3057, h3291, h3293, h3301, hc34, hlam, hphi, u4elo1]
                                · linarith only [h3057, h3291, h3300, hlam]
                              · linarith only [h2766, h3290, h3299, hlam]
                            · linarith only [h0, h2766, h3298, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h3057, h3291, h3293, h3297, hlam]
                        · linarith only [h1314, h3290, h3296, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1314, h3295, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2766, h3292, h3294, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2766, h3292, h3293, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3337 | h3337
                  · linarith only [h0, h3057, h3292, h3337, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3337, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3340 | h3340
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3341 | h3341
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3342 | h3342
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3343 | h3343
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3344 | h3344
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3345 | h3345
                          · linarith only [h3291, h3345, hc04, hlam, hphi, u4elo1]
                          · linarith only [h3057, h3341, h3345, hc02, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h0, h3057, h3290, h3341, h3343, h3344, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1314, h3343, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2766, h3340, h3342, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2766, h3340, h3341, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3352 | h3352
                  · linarith only [h0, h3057, h3340, h3352, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3352, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3355 | h3355
              · linarith only [h3289, h3290, h3355, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3357 | h3357
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3358 | h3358
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3359 | h3359
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3360 | h3360
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3361 | h3361
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3362 | h3362
                          · linarith only [h3355, h3362, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h3362, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3365 | h3365
                          · linarith only [h0, h3057, h3355, h3365, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h1838, h3365, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h1314, h3289, h3360, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h2766, h3357, h3359, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2766, h3357, h3358, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3371 | h3371
                  · linarith only [h0, h3057, h3357, h3371, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3371, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3374 | h3374
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3375 | h3375
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3376 | h3376
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3377 | h3377
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3378 | h3378
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3379 | h3379
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3380 | h3380
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3381 | h3381
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3382 | h3382
                            · linarith only [h0, h3214, h3289, h3374, h3376, h3382, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h2766, h3379, h3382, hc01, hc13, hlam, hphi]
                          · linarith only [h3375, h3381, hc14, hlam, hphi, u4elo0]
                        · linarith only [h3289, h3374, h3380, hc13, hc34, hlam, hphi]
                      · linarith only [h0, h2766, h3376, h3379, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2766, h3376, h3378, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2766, h3376, h3377, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3390 | h3390
                  · linarith only [h0, h3057, h3376, h3390, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3390, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h3289, h3374, h3375, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3394 | h3394
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3395 | h3395
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3396 | h3396
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3397 | h3397
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3398 | h3398
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3399 | h3399
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3400 | h3400
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3401 | h3401
                            · linarith only [h0, h2766, h3289, h3395, h3401, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h2766, h3398, h3401, hc01, hc13, hlam, hphi]
                          · linarith only [h3394, h3400, hc14, hlam, hphi, u4elo0]
                        · linarith only [h0, h2766, h3289, h3398, h3399, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1314, h3398, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2766, h3395, h3397, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2766, h3395, h3396, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3409 | h3409
                  · linarith only [h0, h3057, h3395, h3409, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3409, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3412 | h3412
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3413 | h3413
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3414 | h3414
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3415 | h3415
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3416 | h3416
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3417 | h3417
                          · linarith only [h3394, h3417, hc04, hlam, hphi, u4elo1]
                          · linarith only [h1838, h3417, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h2766, h3289, h3415, h3416, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1314, h3415, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2766, h3412, h3414, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2766, h3412, h3413, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3424 | h3424
                  · linarith only [h0, h3057, h3412, h3424, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3424, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

set_option maxHeartbeats 6854000 in
set_option maxHeartbeats 6854000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1838 | h1838
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h1314 h1838
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h1314 h1838

set_option maxHeartbeats 6854000 in
set_option maxHeartbeats 6854000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1314 | h1314
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x1_x0 m hb0 hb1 hb3 hb4 h0 h1314
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x1_x1 m hb0 hb1 hb3 hb4 h0 h1314

set_option maxHeartbeats 6854000 in
set_option maxHeartbeats 6854000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
