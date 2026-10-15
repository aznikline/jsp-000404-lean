import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6940000 in
set_option maxHeartbeats 6940000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2572 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2574 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2576 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2578 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2579 | h2579
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2580 | h2580
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2581 | h2581
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2582 | h2582
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2583 | h2583
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2584 | h2584
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2585 | h2585
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2586 | h2586
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2587 | h2587
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2588 | h2588
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2589 | h2589
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2590 | h2590
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2591 | h2591
                          · rcases h3bigk with h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c | h2592c
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2572, hlam, p2592_1]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2578, h2588, h2591, hc02, hc45, hlam, hphi, ht0b, ht5b, p2592_1]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              rcases p2592_3 (m.d 0 3) (by simp) with h2596 | h2596
                              · rcases p2592_3 (m.d 1 3) (by simp) with h2597 | h2597
                                · rcases p2592_3 (m.d 2 3) (by simp) with h2598 | h2598
                                  · linarith only [h2578, h2598, hlam]
                                  · linarith only [h2588, h2598, hlam]
                                · linarith only [h2585, h2597, hlam]
                              · linarith only [h2596, hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              rcases p2592_3 (m.d 0 3) (by simp) with h2603 | h2603
                              · rcases p2592_3 (m.d 1 3) (by simp) with h2604 | h2604
                                · rcases p2592_3 (m.d 2 3) (by simp) with h2605 | h2605
                                  · linarith only [h2578, h2605, hlam]
                                  · linarith only [h2589, h2605, hlam]
                                · linarith only [h2586, h2604, hlam]
                              · linarith only [h2603, hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2572, h2583, hc12, hlam, hphi, p2592_1, u1ehi0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2583, h2588, h2591, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2592_1]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              rcases p2592_3 (m.d 0 3) (by simp) with h2613 | h2613
                              · linarith only [h2572, h2613, hlam]
                              · linarith only [h2580, h2613, hlam]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              rcases p2592_3 (m.d 0 3) (by simp) with h2616 | h2616
                              · linarith only [h2572, h2616, hlam]
                              · linarith only [h2581, h2616, hlam]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2578, hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2583, hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h0, h2578, h2591, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2592_1]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              rcases p2592_3 (m.d 0 3) (by simp) with h2623 | h2623
                              · rcases p2592_3 (m.d 1 3) (by simp) with h2624 | h2624
                                · rcases p2592_3 (m.d 2 3) (by simp) with h2625 | h2625
                                  · rcases p2592_3 (m.d 3 4) (by simp) with h2626 | h2626
                                    · linarith only [h2588, h2626, hlam]
                                    · linarith only [h2591, h2626, hlam]
                                  · linarith only [h2625, hlam, p2592_0]
                                · linarith only [h2586, h2624, hlam]
                              · linarith only [h2581, h2623, hlam]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2580, hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2585, hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2588, hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h0, h2578, h2588, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2592_1]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2581, hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2586, hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2589, hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [h2591, hlam, p2592_0]
                            · have p2592_0 := h2592c.1
                              have p2592_1 := h2592c.2.1
                              have p2592_2 := h2592c.2.2.1
                              have p2592_3 := h2592c.2.2.2
                              linarith only [hlam, p2592_0]
                          · rcases h3bigk with h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c | h2642c
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2572, hlam, p2642_1]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2572, h2583, h2588, h2590, h2591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2642_1]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              rcases p2642_3 (m.d 0 3) (by simp) with h2646 | h2646
                              · rcases p2642_3 (m.d 1 3) (by simp) with h2647 | h2647
                                · rcases p2642_3 (m.d 2 3) (by simp) with h2648 | h2648
                                  · linarith only [h2578, h2648, hlam]
                                  · linarith only [h2588, h2648, hlam]
                                · linarith only [h2585, h2647, hlam]
                              · linarith only [h2646, hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              rcases p2642_3 (m.d 0 3) (by simp) with h2653 | h2653
                              · rcases p2642_3 (m.d 1 3) (by simp) with h2654 | h2654
                                · rcases p2642_3 (m.d 2 3) (by simp) with h2655 | h2655
                                  · linarith only [h2578, h2655, hlam]
                                  · linarith only [h2589, h2655, hlam]
                                · linarith only [h2586, h2654, hlam]
                              · linarith only [h2653, hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2572, h2583, hc12, hlam, hphi, p2642_1, u1ehi0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2583, h2588, h2590, h2591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2642_1]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              rcases p2642_3 (m.d 0 3) (by simp) with h2663 | h2663
                              · linarith only [h2572, h2663, hlam]
                              · linarith only [h2580, h2663, hlam]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              rcases p2642_3 (m.d 0 3) (by simp) with h2666 | h2666
                              · linarith only [h2572, h2666, hlam]
                              · linarith only [h2581, h2666, hlam]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2578, hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2583, hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              rcases p2642_3 (m.d 0 3) (by simp) with h2672 | h2672
                              · rcases p2642_3 (m.d 1 3) (by simp) with h2673 | h2673
                                · rcases p2642_3 (m.d 2 3) (by simp) with h2674 | h2674
                                  · rcases p2642_3 (m.d 3 4) (by simp) with h2675 | h2675
                                    · linarith only [h2675, hlam, p2642_0]
                                    · rcases p2642_3 (m.d 3 5) (by simp) with h2677 | h2677
                                      · linarith only [h2589, h2677, hlam]
                                      · linarith only [h2591, h2677, hlam]
                                  · linarith only [h2674, hlam, p2642_0]
                                · linarith only [h2585, h2673, hlam]
                              · linarith only [h2580, h2672, hlam]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              rcases p2642_3 (m.d 0 3) (by simp) with h2683 | h2683
                              · rcases p2642_3 (m.d 1 3) (by simp) with h2684 | h2684
                                · rcases p2642_3 (m.d 2 3) (by simp) with h2685 | h2685
                                  · rcases p2642_3 (m.d 3 4) (by simp) with h2686 | h2686
                                    · linarith only [h2588, h2686, hlam]
                                    · rcases p2642_3 (m.d 3 5) (by simp) with h2688 | h2688
                                      · linarith only [h2688, hlam, p2642_0]
                                      · rcases h5bigk with h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [hlam, p2690_0]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2576, hlam, p2690_1]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2580, h2582, h2590, h2591, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2690_1]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          rcases p2690_3 (m.d 0 5) (by simp) with h2694 | h2694
                                          · rcases p2690_3 (m.d 1 5) (by simp) with h2695 | h2695
                                            · rcases p2690_3 (m.d 2 5) (by simp) with h2696 | h2696
                                              · linarith only [h2579, h2696, hlam]
                                              · linarith only [h2589, h2696, hlam]
                                            · linarith only [h2586, h2695, hlam]
                                          · linarith only [h2581, h2694, hlam]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h0, h2578, h2580, h2582, h2591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2690_1]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2576, h2583, h2585, h2587, hc12, hlam, hphi, p2690_1, u1ehi0]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [hlam, p2690_0]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2583, h2585, h2587, h2590, h2591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2690_1]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          rcases p2690_3 (m.d 0 5) (by simp) with h2705 | h2705
                                          · linarith only [h2576, h2705, hlam]
                                          · linarith only [h2581, h2705, hlam]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2583, h2585, h2587, h2591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2690_1]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2579, hlam, p2690_1]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2584, hlam, p2690_1]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [hlam, p2690_0]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h0, h2579, h2591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2690_1]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h0, h2578, h2588, h2590, h2591, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2690_1]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2581, hlam, p2690_0]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2586, hlam, p2690_0]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2589, hlam, p2690_0]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [hlam, p2690_0]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2591, hlam, p2690_1]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2582, hlam, p2690_0]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2587, hlam, p2690_0]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2590, hlam, p2690_0]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [h2591, hc34, hc45, hlam, hphi, p2690_1]
                                        · have p2690_0 := h2690c.1
                                          have p2690_1 := h2690c.2.1
                                          have p2690_2 := h2690c.2.2.1
                                          have p2690_3 := h2690c.2.2.2
                                          linarith only [hlam, p2690_0]
                                  · linarith only [h2685, hlam, p2642_0]
                                · linarith only [h2586, h2684, hlam]
                              · linarith only [h2581, h2683, hlam]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2580, hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2585, hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2588, hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2591, hlam, p2642_1]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2581, hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2586, hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h2589, hlam, p2642_0]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [h0, h2578, h2589, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2642_1]
                            · have p2642_0 := h2642c.1
                              have p2642_1 := h2642c.2.1
                              have p2642_2 := h2642c.2.2.1
                              have p2642_3 := h2642c.2.2.2
                              linarith only [hlam, p2642_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2737 | h2737
                          · linarith only [h0, h2578, h2588, h2590, h2737, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases h3bigk with h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h2572, hlam, p2739_1]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              rcases p2739_3 (m.d 0 3) (by simp) with h2742 | h2742
                              · rcases p2739_3 (m.d 1 3) (by simp) with h2743 | h2743
                                · rcases p2739_3 (m.d 2 3) (by simp) with h2744 | h2744
                                  · linarith only [h2578, h2744, hlam]
                                  · rcases p2739_3 (m.d 3 4) (by simp) with h2746 | h2746
                                    · linarith only [h2580, h2746, hlam]
                                    · rcases p2739_3 (m.d 3 5) (by simp) with h2748 | h2748
                                      · linarith only [h2581, h2748, hlam]
                                      · rcases h5bigk with h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2576, hlam, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          rcases p2750_3 (m.d 0 5) (by simp) with h2753 | h2753
                                          · rcases p2750_3 (m.d 1 5) (by simp) with h2754 | h2754
                                            · rcases p2750_3 (m.d 2 5) (by simp) with h2755 | h2755
                                              · linarith only [h2579, h2755, hlam]
                                              · rcases p2750_3 (m.d 3 5) (by simp) with h2757 | h2757
                                                · linarith only [h2581, h2757, hlam]
                                                · rcases p2750_3 (m.d 4 5) (by simp) with h2759 | h2759
                                                  · linarith only [h2582, h2759, hlam]
                                                  · linarith only [h2590, h2759, hlam]
                                            · linarith only [h2584, h2754, hlam]
                                          · linarith only [h2579, h2753, hlam]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          rcases p2750_3 (m.d 0 5) (by simp) with h2764 | h2764
                                          · rcases p2750_3 (m.d 1 5) (by simp) with h2765 | h2765
                                            · rcases p2750_3 (m.d 2 5) (by simp) with h2766 | h2766
                                              · linarith only [h2579, h2766, hlam]
                                              · linarith only [h2589, h2766, hlam]
                                            · linarith only [h2586, h2765, hlam]
                                          · linarith only [h2581, h2764, hlam]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2588, h2590, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2576, h2583, h2585, h2587, hc12, hlam, hphi, p2750_1, u1ehi0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          rcases p2750_3 (m.d 0 5) (by simp) with h2774 | h2774
                                          · linarith only [h2576, h2774, hlam]
                                          · linarith only [h2579, h2774, hlam]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          rcases p2750_3 (m.d 0 5) (by simp) with h2777 | h2777
                                          · linarith only [h2576, h2777, hlam]
                                          · linarith only [h2581, h2777, hlam]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2583, h2585, h2587, h2588, h2590, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2579, hlam, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2584, hlam, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h0, h2579, h2737, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2590, hlam, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2581, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2586, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2589, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2737, hlam, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2582, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2587, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h0, h2578, h2580, h2582, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h0, h2578, h2580, h2582, h2737, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [hlam, p2750_0]
                                · linarith only [h2583, h2743, hlam]
                              · linarith only [h2578, h2742, hlam]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              rcases p2739_3 (m.d 0 3) (by simp) with h2798 | h2798
                              · rcases p2739_3 (m.d 1 3) (by simp) with h2799 | h2799
                                · rcases p2739_3 (m.d 2 3) (by simp) with h2800 | h2800
                                  · linarith only [h2578, h2800, hlam]
                                  · linarith only [h2588, h2800, hlam]
                                · linarith only [h2585, h2799, hlam]
                              · linarith only [h2798, hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              rcases p2739_3 (m.d 0 3) (by simp) with h2805 | h2805
                              · rcases p2739_3 (m.d 1 3) (by simp) with h2806 | h2806
                                · rcases p2739_3 (m.d 2 3) (by simp) with h2807 | h2807
                                  · linarith only [h2578, h2807, hlam]
                                  · linarith only [h2589, h2807, hlam]
                                · linarith only [h2586, h2806, hlam]
                              · linarith only [h2805, hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h2572, h2583, hc12, hlam, hphi, p2739_1, u1ehi0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              rcases p2739_3 (m.d 0 3) (by simp) with h2814 | h2814
                              · linarith only [h2572, h2814, hlam]
                              · linarith only [h2578, h2814, hlam]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              rcases p2739_3 (m.d 0 3) (by simp) with h2817 | h2817
                              · linarith only [h2572, h2817, hlam]
                              · linarith only [h2580, h2817, hlam]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              rcases p2739_3 (m.d 0 3) (by simp) with h2820 | h2820
                              · linarith only [h2572, h2820, hlam]
                              · linarith only [h2581, h2820, hlam]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h2578, hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h2583, hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              rcases p2739_3 (m.d 0 3) (by simp) with h2826 | h2826
                              · rcases p2739_3 (m.d 1 3) (by simp) with h2827 | h2827
                                · rcases p2739_3 (m.d 2 3) (by simp) with h2828 | h2828
                                  · rcases p2739_3 (m.d 3 4) (by simp) with h2829 | h2829
                                    · linarith only [h2829, hlam, p2739_0]
                                    · rcases p2739_3 (m.d 3 5) (by simp) with h2831 | h2831
                                      · linarith only [h2589, h2831, hlam]
                                      · linarith only [h2737, h2831, hlam]
                                  · linarith only [h2828, hlam, p2739_0]
                                · linarith only [h2585, h2827, hlam]
                              · linarith only [h2580, h2826, hlam]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              rcases p2739_3 (m.d 0 3) (by simp) with h2837 | h2837
                              · rcases p2739_3 (m.d 1 3) (by simp) with h2838 | h2838
                                · rcases p2739_3 (m.d 2 3) (by simp) with h2839 | h2839
                                  · rcases p2739_3 (m.d 3 4) (by simp) with h2840 | h2840
                                    · linarith only [h2588, h2840, hlam]
                                    · rcases p2739_3 (m.d 3 5) (by simp) with h2842 | h2842
                                      · linarith only [h2842, hlam, p2739_0]
                                      · rcases h5bigk with h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c | h2844c
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [hlam, p2844_0]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2576, hlam, p2844_1]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          rcases p2844_3 (m.d 0 5) (by simp) with h2847 | h2847
                                          · rcases p2844_3 (m.d 1 5) (by simp) with h2848 | h2848
                                            · rcases p2844_3 (m.d 2 5) (by simp) with h2849 | h2849
                                              · linarith only [h2579, h2849, hlam]
                                              · rcases p2844_3 (m.d 3 5) (by simp) with h2851 | h2851
                                                · linarith only [h2581, h2851, hlam]
                                                · rcases p2844_3 (m.d 4 5) (by simp) with h2853 | h2853
                                                  · linarith only [h2582, h2853, hlam]
                                                  · linarith only [h2590, h2853, hlam]
                                            · linarith only [h2584, h2848, hlam]
                                          · linarith only [h2579, h2847, hlam]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          rcases p2844_3 (m.d 0 5) (by simp) with h2858 | h2858
                                          · rcases p2844_3 (m.d 1 5) (by simp) with h2859 | h2859
                                            · rcases p2844_3 (m.d 2 5) (by simp) with h2860 | h2860
                                              · linarith only [h2579, h2860, hlam]
                                              · linarith only [h2589, h2860, hlam]
                                            · linarith only [h2586, h2859, hlam]
                                          · linarith only [h2581, h2858, hlam]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2580, h2582, h2588, h2590, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2844_1]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2576, h2585, h2587, hc13, hlam, hphi, p2844_1, u1ehi0]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [hlam, p2844_0]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          rcases p2844_3 (m.d 0 5) (by simp) with h2868 | h2868
                                          · linarith only [h2576, h2868, hlam]
                                          · linarith only [h2579, h2868, hlam]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          rcases p2844_3 (m.d 0 5) (by simp) with h2871 | h2871
                                          · linarith only [h2576, h2871, hlam]
                                          · linarith only [h2581, h2871, hlam]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2583, h2585, h2587, h2588, h2590, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2844_1]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2579, hlam, p2844_1]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2584, hlam, p2844_1]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [hlam, p2844_0]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h0, h2579, h2737, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2844_1]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2590, hlam, p2844_1]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2581, hlam, p2844_0]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2586, hlam, p2844_0]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2589, hlam, p2844_0]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [hlam, p2844_0]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2737, hlam, p2844_1]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2582, hlam, p2844_0]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h2587, hlam, p2844_0]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h0, h2578, h2580, h2582, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2844_1]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [h0, h2578, h2580, h2582, h2737, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2844_1]
                                        · have p2844_0 := h2844c.1
                                          have p2844_1 := h2844c.2.1
                                          have p2844_2 := h2844c.2.2.1
                                          have p2844_3 := h2844c.2.2.2
                                          linarith only [hlam, p2844_0]
                                  · linarith only [h2839, hlam, p2739_0]
                                · linarith only [h2586, h2838, hlam]
                              · linarith only [h2581, h2837, hlam]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h2580, hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h2585, hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h2588, hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h2737, hlam, p2739_1]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h2581, hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h2586, hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h2589, hlam, p2739_0]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [h0, h2578, h2589, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2739_1]
                            · have p2739_0 := h2739c.1
                              have p2739_1 := h2739c.2.1
                              have p2739_2 := h2739c.2.2.1
                              have p2739_3 := h2739c.2.2.2
                              linarith only [hlam, p2739_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2903 | h2903
                        · linarith only [h2588, h2589, h2903, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2905 | h2905
                          · linarith only [h2588, h2589, h2903, h2905, hlam]
                          · rcases h3bigk with h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2572, hlam, p2907_1]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              rcases p2907_3 (m.d 0 3) (by simp) with h2910 | h2910
                              · rcases p2907_3 (m.d 1 3) (by simp) with h2911 | h2911
                                · rcases p2907_3 (m.d 2 3) (by simp) with h2912 | h2912
                                  · linarith only [h2578, h2912, hlam]
                                  · rcases p2907_3 (m.d 3 4) (by simp) with h2914 | h2914
                                    · linarith only [h2580, h2914, hlam]
                                    · rcases p2907_3 (m.d 3 5) (by simp) with h2916 | h2916
                                      · linarith only [h2581, h2916, hlam]
                                      · linarith only [h2589, h2916, hlam]
                                · linarith only [h2583, h2911, hlam]
                              · linarith only [h2578, h2910, hlam]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2580, h2582, h2588, h2589, h2905, hlam, p2907_2]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h0, h2578, h2588, h2589, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2907_1]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2572, h2583, hc12, hlam, hphi, p2907_1, u1ehi0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              rcases p2907_3 (m.d 0 3) (by simp) with h2925 | h2925
                              · linarith only [h2572, h2925, hlam]
                              · linarith only [h2578, h2925, hlam]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2572, h2580, h2582, h2588, h2589, h2905, hlam, p2907_2]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2588, h2589, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2907_1]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2578, hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2583, hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2580, h2582, h2589, h2905, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2907_1]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2589, hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2580, hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2585, hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2588, hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2905, hlam, p2907_1]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2581, hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h2586, hlam, p2907_0]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [h0, h2578, h2580, h2582, h2588, h2905, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2907_1]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              rcases p2907_3 (m.d 0 3) (by simp) with h2943 | h2943
                              · rcases p2907_3 (m.d 1 3) (by simp) with h2944 | h2944
                                · rcases p2907_3 (m.d 2 3) (by simp) with h2945 | h2945
                                  · linarith only [h2589, h2945, hlam]
                                  · linarith only [h2588, h2945, hlam]
                                · linarith only [h2585, h2944, hlam]
                              · linarith only [h2580, h2943, hlam]
                            · have p2907_0 := h2907c.1
                              have p2907_1 := h2907c.2.1
                              have p2907_2 := h2907c.2.2.1
                              have p2907_3 := h2907c.2.2.2
                              linarith only [hlam, p2907_0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2951 | h2951
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2952 | h2952
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2953 | h2953
                          · rcases h3bigk with h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2572, hlam, p2954_1]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              rcases p2954_3 (m.d 0 3) (by simp) with h2957 | h2957
                              · rcases p2954_3 (m.d 1 3) (by simp) with h2958 | h2958
                                · rcases p2954_3 (m.d 2 3) (by simp) with h2959 | h2959
                                  · linarith only [h2578, h2959, hlam]
                                  · rcases p2954_3 (m.d 3 4) (by simp) with h2961 | h2961
                                    · linarith only [h2580, h2961, hlam]
                                    · linarith only [h2588, h2961, hlam]
                                · linarith only [h2583, h2958, hlam]
                              · linarith only [h2578, h2957, hlam]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h0, h2578, h2588, h2951, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2954_1]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2580, h2588, h2951, hlam, p2954_2]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2572, h2583, hc12, hlam, hphi, p2954_1, u1ehi0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              rcases p2954_3 (m.d 0 3) (by simp) with h2970 | h2970
                              · linarith only [h2572, h2970, hlam]
                              · linarith only [h2578, h2970, hlam]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2583, h2588, h2951, h2953, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2954_1]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2572, h2580, h2588, h2951, hlam, p2954_2]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2578, hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2583, hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2588, hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2580, h2588, h2953, hc03, hc45, hlam, hphi, ht0b, ht5b, p2954_1]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2580, hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2585, hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h0, h2578, h2580, h2951, h2953, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2954_1]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              rcases p2954_3 (m.d 0 3) (by simp) with h2984 | h2984
                              · rcases p2954_3 (m.d 1 3) (by simp) with h2985 | h2985
                                · rcases p2954_3 (m.d 2 3) (by simp) with h2986 | h2986
                                  · linarith only [h2588, h2986, hlam]
                                  · linarith only [h2951, h2986, hlam]
                                · linarith only [h2586, h2985, hlam]
                              · linarith only [h2581, h2984, hlam]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2581, hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2586, hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2951, hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [h2953, hlam, p2954_0]
                            · have p2954_0 := h2954c.1
                              have p2954_1 := h2954c.2.1
                              have p2954_2 := h2954c.2.2.1
                              have p2954_3 := h2954c.2.2.2
                              linarith only [hlam, p2954_0]
                          · linarith only [h2582, h2588, h2951, h2953, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h2588, h2951, h2952, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2998 | h2998
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2999 | h2999
                          · rcases h3bigk with h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c | h3000c
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2572, hlam, p3000_1]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              rcases p3000_3 (m.d 0 3) (by simp) with h3003 | h3003
                              · rcases p3000_3 (m.d 1 3) (by simp) with h3004 | h3004
                                · rcases p3000_3 (m.d 2 3) (by simp) with h3005 | h3005
                                  · linarith only [h2578, h3005, hlam]
                                  · rcases p3000_3 (m.d 3 4) (by simp) with h3007 | h3007
                                    · linarith only [h2580, h3007, hlam]
                                    · linarith only [h2588, h3007, hlam]
                                · linarith only [h2583, h3004, hlam]
                              · linarith only [h2578, h3003, hlam]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              rcases p3000_3 (m.d 0 3) (by simp) with h3012 | h3012
                              · rcases p3000_3 (m.d 1 3) (by simp) with h3013 | h3013
                                · rcases p3000_3 (m.d 2 3) (by simp) with h3014 | h3014
                                  · linarith only [h2578, h3014, hlam]
                                  · rcases p3000_3 (m.d 3 4) (by simp) with h3016 | h3016
                                    · linarith only [h3016, hlam, p3000_0]
                                    · rcases p3000_3 (m.d 3 5) (by simp) with h3018 | h3018
                                      · linarith only [h2581, h3018, hlam]
                                      · rcases h5bigk with h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c | h3020c
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [hlam, p3020_0]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2576, hlam, p3020_1]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          rcases p3020_3 (m.d 0 5) (by simp) with h3023 | h3023
                                          · rcases p3020_3 (m.d 1 5) (by simp) with h3024 | h3024
                                            · rcases p3020_3 (m.d 2 5) (by simp) with h3025 | h3025
                                              · linarith only [h2579, h3025, hlam]
                                              · rcases p3020_3 (m.d 3 5) (by simp) with h3027 | h3027
                                                · linarith only [h2581, h3027, hlam]
                                                · linarith only [h2951, h3027, hlam]
                                            · linarith only [h2584, h3024, hlam]
                                          · linarith only [h2579, h3023, hlam]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2576, h2583, h2585, h2587, h2951, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3020_1]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          rcases p3020_3 (m.d 0 5) (by simp) with h3033 | h3033
                                          · rcases p3020_3 (m.d 1 5) (by simp) with h3034 | h3034
                                            · rcases p3020_3 (m.d 2 5) (by simp) with h3035 | h3035
                                              · linarith only [h2579, h3035, hlam]
                                              · linarith only [h2998, h3035, hlam]
                                            · linarith only [h2587, h3034, hlam]
                                          · linarith only [h2582, h3033, hlam]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2576, h2583, h2585, h2587, hc12, hlam, hphi, p3020_1, u1ehi0]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [hlam, p3020_0]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          rcases p3020_3 (m.d 0 5) (by simp) with h3042 | h3042
                                          · linarith only [h2576, h3042, hlam]
                                          · linarith only [h2579, h3042, hlam]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2583, h2585, h2587, h2951, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3020_1]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          rcases p3020_3 (m.d 0 5) (by simp) with h3046 | h3046
                                          · linarith only [h2576, h3046, hlam]
                                          · linarith only [h2582, h3046, hlam]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2579, hlam, p3020_1]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2584, hlam, p3020_1]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [hlam, p3020_0]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2951, hlam, p3020_1]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h0, h2579, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3020_1]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2581, hlam, p3020_0]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2586, hlam, p3020_0]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h0, h2578, h2581, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3020_1]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [hlam, p3020_0]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h0, h2578, h2999, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3000_1, p3020_1]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2582, hlam, p3020_0]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2587, hlam, p3020_0]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2998, hlam, p3020_0]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [h2999, hlam, p3020_0]
                                        · have p3020_0 := h3020c.1
                                          have p3020_1 := h3020c.2.1
                                          have p3020_2 := h3020c.2.2.1
                                          have p3020_3 := h3020c.2.2.2
                                          linarith only [hlam, p3020_0]
                                · linarith only [h2585, h3013, hlam]
                              · linarith only [h3012, hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              rcases p3000_3 (m.d 0 3) (by simp) with h3066 | h3066
                              · rcases p3000_3 (m.d 1 3) (by simp) with h3067 | h3067
                                · rcases p3000_3 (m.d 2 3) (by simp) with h3068 | h3068
                                  · linarith only [h2578, h3068, hlam]
                                  · rcases p3000_3 (m.d 3 4) (by simp) with h3070 | h3070
                                    · linarith only [h2580, h3070, hlam]
                                    · linarith only [h2999, h3070, hlam]
                                · linarith only [h2586, h3067, hlam]
                              · linarith only [h3066, hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2572, h2583, hc12, hlam, hphi, p3000_1, u1ehi0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              rcases p3000_3 (m.d 0 3) (by simp) with h3077 | h3077
                              · linarith only [h2572, h3077, hlam]
                              · linarith only [h2578, h3077, hlam]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              rcases p3000_3 (m.d 0 3) (by simp) with h3080 | h3080
                              · linarith only [h2572, h3080, hlam]
                              · linarith only [h2580, h3080, hlam]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              rcases p3000_3 (m.d 0 3) (by simp) with h3083 | h3083
                              · linarith only [h2572, h3083, hlam]
                              · linarith only [h2581, h3083, hlam]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2578, hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2583, hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2588, hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2951, hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2580, hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2585, hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              rcases p3000_3 (m.d 0 3) (by simp) with h3093 | h3093
                              · rcases p3000_3 (m.d 1 3) (by simp) with h3094 | h3094
                                · rcases p3000_3 (m.d 2 3) (by simp) with h3095 | h3095
                                  · linarith only [h3095, hlam, p3000_0]
                                  · rcases p3000_3 (m.d 3 4) (by simp) with h3097 | h3097
                                    · rcases p3000_3 (m.d 3 5) (by simp) with h3098 | h3098
                                      · linarith only [h2999, h3098, hlam]
                                      · linarith only [h2951, h3098, hlam]
                                    · linarith only [h3097, hlam, p3000_0]
                                · linarith only [h2583, h3094, hlam]
                              · linarith only [h2578, h3093, hlam]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2580, h2951, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3000_1]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2581, hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2586, hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              rcases p3000_3 (m.d 0 3) (by simp) with h3108 | h3108
                              · rcases p3000_3 (m.d 1 3) (by simp) with h3109 | h3109
                                · rcases p3000_3 (m.d 2 3) (by simp) with h3110 | h3110
                                  · linarith only [h3110, hlam, p3000_0]
                                  · rcases p3000_3 (m.d 3 4) (by simp) with h3112 | h3112
                                    · rcases p3000_3 (m.d 3 5) (by simp) with h3113 | h3113
                                      · rcases h5bigk with h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [hlam, p3114_0]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2576, hlam, p3114_1]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          rcases p3114_3 (m.d 0 5) (by simp) with h3117 | h3117
                                          · rcases p3114_3 (m.d 1 5) (by simp) with h3118 | h3118
                                            · rcases p3114_3 (m.d 2 5) (by simp) with h3119 | h3119
                                              · linarith only [h2579, h3119, hlam]
                                              · rcases p3114_3 (m.d 3 5) (by simp) with h3121 | h3121
                                                · linarith only [h2581, h3121, hlam]
                                                · linarith only [h2951, h3121, hlam]
                                            · linarith only [h2584, h3118, hlam]
                                          · linarith only [h2579, h3117, hlam]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3000_1, p3114_1]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          rcases p3114_3 (m.d 0 5) (by simp) with h3127 | h3127
                                          · rcases p3114_3 (m.d 1 5) (by simp) with h3128 | h3128
                                            · rcases p3114_3 (m.d 2 5) (by simp) with h3129 | h3129
                                              · linarith only [h2579, h3129, hlam]
                                              · linarith only [h2998, h3129, hlam]
                                            · linarith only [h2587, h3128, hlam]
                                          · linarith only [h2582, h3127, hlam]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2576, h2583, h2585, h2587, hc12, hlam, hphi, p3114_1, u1ehi0]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [hlam, p3114_0]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          rcases p3114_3 (m.d 0 5) (by simp) with h3136 | h3136
                                          · linarith only [h2576, h3136, hlam]
                                          · linarith only [h2579, h3136, hlam]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2583, h2585, h2587, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3000_1, p3114_1]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          rcases p3114_3 (m.d 0 5) (by simp) with h3140 | h3140
                                          · linarith only [h2576, h3140, hlam]
                                          · linarith only [h2582, h3140, hlam]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2579, hlam, p3114_1]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2584, hlam, p3114_1]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [hlam, p3114_0]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2951, hlam, p3114_1]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h0, h2579, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3114_1]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2581, hlam, p3114_0]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2586, hlam, p3114_0]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2572, h2581, h2583, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3114_1]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [hlam, p3114_0]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2572, h2580, h2583, h2999, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3114_1]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2582, hlam, p3114_0]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2587, hlam, p3114_0]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2998, hlam, p3114_0]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [h2999, hlam, p3114_0]
                                        · have p3114_0 := h3114c.1
                                          have p3114_1 := h3114c.2.1
                                          have p3114_2 := h3114c.2.2.1
                                          have p3114_3 := h3114c.2.2.2
                                          linarith only [hlam, p3114_0]
                                      · linarith only [h3113, hlam, p3000_0]
                                    · linarith only [h2588, h3112, hlam]
                                · linarith only [h2583, h3109, hlam]
                              · linarith only [h2578, h3108, hlam]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [h2999, hlam, p3000_0]
                            · have p3000_0 := h3000c.1
                              have p3000_1 := h3000c.2.1
                              have p3000_2 := h3000c.2.2.1
                              have p3000_3 := h3000c.2.2.2
                              linarith only [hlam, p3000_0]
                          · linarith only [h2588, h2998, h2999, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3165 | h3165
                          · rcases h3bigk with h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c | h3166c
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2572, hlam, p3166_1]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2580, h2588, h2998, h3165, hlam, p3166_2]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2572, h2583, h2588, h2998, h3165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3166_1]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              rcases p3166_3 (m.d 0 3) (by simp) with h3171 | h3171
                              · rcases p3166_3 (m.d 1 3) (by simp) with h3172 | h3172
                                · rcases p3166_3 (m.d 2 3) (by simp) with h3173 | h3173
                                  · linarith only [h2578, h3173, hlam]
                                  · rcases p3166_3 (m.d 3 4) (by simp) with h3175 | h3175
                                    · linarith only [h2580, h3175, hlam]
                                    · linarith only [h3165, h3175, hlam]
                                · linarith only [h2586, h3172, hlam]
                              · linarith only [h3171, hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2572, h2583, hc12, hlam, hphi, p3166_1, u1ehi0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2572, h2580, h2588, h2998, h3165, hlam, p3166_2]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2588, h2998, h3165, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3166_1]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              rcases p3166_3 (m.d 0 3) (by simp) with h3184 | h3184
                              · linarith only [h2572, h3184, hlam]
                              · linarith only [h2581, h3184, hlam]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2578, hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2583, hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2588, hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2951, hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2580, hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2585, hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              rcases p3166_3 (m.d 0 3) (by simp) with h3194 | h3194
                              · rcases p3166_3 (m.d 1 3) (by simp) with h3195 | h3195
                                · rcases p3166_3 (m.d 2 3) (by simp) with h3196 | h3196
                                  · linarith only [h3196, hlam, p3166_0]
                                  · rcases p3166_3 (m.d 3 4) (by simp) with h3198 | h3198
                                    · rcases p3166_3 (m.d 3 5) (by simp) with h3199 | h3199
                                      · linarith only [h3165, h3199, hlam]
                                      · linarith only [h2951, h3199, hlam]
                                    · linarith only [h3198, hlam, p3166_0]
                                · linarith only [h2583, h3195, hlam]
                              · linarith only [h2578, h3194, hlam]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2580, h2588, h2998, h3165, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3166_1]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2581, hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h2586, hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              rcases p3166_3 (m.d 0 3) (by simp) with h3209 | h3209
                              · rcases p3166_3 (m.d 1 3) (by simp) with h3210 | h3210
                                · rcases p3166_3 (m.d 2 3) (by simp) with h3211 | h3211
                                  · linarith only [h3211, hlam, p3166_0]
                                  · rcases p3166_3 (m.d 3 4) (by simp) with h3213 | h3213
                                    · rcases p3166_3 (m.d 3 5) (by simp) with h3214 | h3214
                                      · rcases h5bigk with h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [hlam, p3215_0]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2576, hlam, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          rcases p3215_3 (m.d 0 5) (by simp) with h3218 | h3218
                                          · rcases p3215_3 (m.d 1 5) (by simp) with h3219 | h3219
                                            · rcases p3215_3 (m.d 2 5) (by simp) with h3220 | h3220
                                              · linarith only [h2579, h3220, hlam]
                                              · rcases p3215_3 (m.d 3 5) (by simp) with h3222 | h3222
                                                · linarith only [h2581, h3222, hlam]
                                                · linarith only [h2951, h3222, hlam]
                                            · linarith only [h2584, h3219, hlam]
                                          · linarith only [h2579, h3218, hlam]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2582, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3166_1, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2574, h2582, h2583, h2585, h2588, h2998, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2576, h2583, h2585, h2587, hc12, hlam, hphi, p3215_1, u1ehi0]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [hlam, p3215_0]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          rcases p3215_3 (m.d 0 5) (by simp) with h3231 | h3231
                                          · linarith only [h2576, h3231, hlam]
                                          · linarith only [h2579, h3231, hlam]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2583, h2585, h2587, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3166_1, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2583, h2585, h2587, h2588, h2998, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2579, hlam, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2584, hlam, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [hlam, p3215_0]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2951, hlam, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2998, hlam, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2581, hlam, p3215_0]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2586, hlam, p3215_0]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2588, h2998, hc23, hc35, hlam, hphi, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [hlam, p3215_0]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2572, h2580, h2583, h2588, h2998, h3165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2582, hlam, p3215_0]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2587, hlam, p3215_0]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h2588, h2998, hc23, hc45, hlam, hphi, ht34, p3215_1]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [h3165, hlam, p3215_0]
                                        · have p3215_0 := h3215c.1
                                          have p3215_1 := h3215c.2.1
                                          have p3215_2 := h3215c.2.2.1
                                          have p3215_3 := h3215c.2.2.2
                                          linarith only [hlam, p3215_0]
                                      · linarith only [h3214, hlam, p3166_0]
                                    · linarith only [h2588, h3213, hlam]
                                · linarith only [h2583, h3210, hlam]
                              · linarith only [h2578, h3209, hlam]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [h3165, hlam, p3166_0]
                            · have p3166_0 := h3166c.1
                              have p3166_1 := h3166c.2.1
                              have p3166_2 := h3166c.2.2.1
                              have p3166_3 := h3166c.2.2.2
                              linarith only [hlam, p3166_0]
                          · rcases h3bigk with h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2572, hlam, p3257_1]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2580, h2582, h2588, h3165, hlam, p3257_2]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              rcases p3257_3 (m.d 0 3) (by simp) with h3261 | h3261
                              · rcases p3257_3 (m.d 1 3) (by simp) with h3262 | h3262
                                · rcases p3257_3 (m.d 2 3) (by simp) with h3263 | h3263
                                  · linarith only [h2578, h3263, hlam]
                                  · rcases p3257_3 (m.d 3 4) (by simp) with h3265 | h3265
                                    · linarith only [h3265, hlam, p3257_0]
                                    · rcases p3257_3 (m.d 3 5) (by simp) with h3267 | h3267
                                      · linarith only [h2581, h3267, hlam]
                                      · linarith only [h3165, h3267, hlam]
                                · linarith only [h2585, h3262, hlam]
                              · linarith only [h3261, hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              rcases p3257_3 (m.d 0 3) (by simp) with h3272 | h3272
                              · rcases p3257_3 (m.d 1 3) (by simp) with h3273 | h3273
                                · rcases p3257_3 (m.d 2 3) (by simp) with h3274 | h3274
                                  · linarith only [h2578, h3274, hlam]
                                  · rcases p3257_3 (m.d 3 4) (by simp) with h3276 | h3276
                                    · linarith only [h2580, h3276, hlam]
                                    · rcases p3257_3 (m.d 3 5) (by simp) with h3278 | h3278
                                      · linarith only [h3278, hlam, p3257_0]
                                      · rcases h5bigk with h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c | h3280c
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [hlam, p3280_0]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2576, hlam, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          rcases p3280_3 (m.d 0 5) (by simp) with h3283 | h3283
                                          · rcases p3280_3 (m.d 1 5) (by simp) with h3284 | h3284
                                            · rcases p3280_3 (m.d 2 5) (by simp) with h3285 | h3285
                                              · linarith only [h2579, h3285, hlam]
                                              · rcases p3280_3 (m.d 3 5) (by simp) with h3287 | h3287
                                                · linarith only [h2581, h3287, hlam]
                                                · linarith only [h2951, h3287, hlam]
                                            · linarith only [h2584, h3284, hlam]
                                          · linarith only [h2579, h3283, hlam]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2581, hlam, p3257_2, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2576, h2583, h2585, h2587, h3165, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2576, h2583, h2585, h2587, hc12, hlam, hphi, p3280_1, u1ehi0]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [hlam, p3280_0]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          rcases p3280_3 (m.d 0 5) (by simp) with h3296 | h3296
                                          · linarith only [h2576, h3296, hlam]
                                          · linarith only [h2579, h3296, hlam]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2583, h2585, h2587, h2588, h3165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2583, h2585, h2587, h2588, h3165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2579, hlam, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2584, hlam, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [hlam, p3280_0]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2951, hlam, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2998, hlam, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2581, hlam, p3280_0]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2586, hlam, p3280_0]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2588, h2998, hc23, hc35, hlam, hphi, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [hlam, p3280_0]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h3165, hlam, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2582, hlam, p3280_0]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2587, hlam, p3280_0]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2580, h2582, h2588, h2998, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [h2572, h2580, h2582, h2583, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3280_1]
                                        · have p3280_0 := h3280c.1
                                          have p3280_1 := h3280c.2.1
                                          have p3280_2 := h3280c.2.2.1
                                          have p3280_3 := h3280c.2.2.2
                                          linarith only [hlam, p3280_0]
                                · linarith only [h2586, h3273, hlam]
                              · linarith only [h3272, hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2572, h2583, hc12, hlam, hphi, p3257_1, u1ehi0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2572, h2580, h2582, h2588, h3165, hlam, p3257_2]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              rcases p3257_3 (m.d 0 3) (by simp) with h3321 | h3321
                              · linarith only [h2572, h3321, hlam]
                              · linarith only [h2580, h3321, hlam]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              rcases p3257_3 (m.d 0 3) (by simp) with h3324 | h3324
                              · linarith only [h2572, h3324, hlam]
                              · linarith only [h2581, h3324, hlam]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2578, hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2583, hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2588, hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2951, hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2580, hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2585, hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2580, h2582, h3165, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3257_1]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h3165, hlam, p3257_1]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2581, hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h2586, hlam, p3257_0]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              rcases p3257_3 (m.d 0 3) (by simp) with h3339 | h3339
                              · rcases p3257_3 (m.d 1 3) (by simp) with h3340 | h3340
                                · rcases p3257_3 (m.d 2 3) (by simp) with h3341 | h3341
                                  · linarith only [h3341, hlam, p3257_0]
                                  · rcases p3257_3 (m.d 3 4) (by simp) with h3343 | h3343
                                    · linarith only [h3165, h3343, hlam]
                                    · linarith only [h2588, h3343, hlam]
                                · linarith only [h2583, h3340, hlam]
                              · linarith only [h2578, h3339, hlam]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [h0, h2578, h2581, h2588, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3257_1]
                            · have p3257_0 := h3257c.1
                              have p3257_1 := h3257c.2.1
                              have p3257_2 := h3257c.2.2.1
                              have p3257_3 := h3257c.2.2.2
                              linarith only [hlam, p3257_0]
                  · linarith only [h0, h2578, h2580, h2582, h2587, hc12, hlam, hphi, u1ehi3]
                · linarith only [h0, h2578, h2581, h2586, hc12, hlam, hphi, u1ehi2]
              · linarith only [h2572, h2585, hc34, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h0, h2584, hc25, hlam, hphi, ht12, u1ehi0]
          · linarith only [h0, h2583, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3355 | h3355
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3356 | h3356
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3357 | h3357
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3358 | h3358
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3359 | h3359
                  · linarith only [h2574, h2582, h3355, h3357, h3359, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h2574, h3359, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                · linarith only [h2572, h3358, hc35, hlam, hphi, ht12, ht23, u1ehi0]
              · linarith only [h2572, h3357, hc34, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h0, h2572, h2579, h2581, h3356, hc13, hlam, hphi, u1ehi0]
          · linarith only [h0, h2578, h3355, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3366 | h3366
        · linarith only [h2580, h2581, h3366, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3368 | h3368
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3369 | h3369
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3370 | h3370
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3371 | h3371
                · linarith only [h2572, h2581, h3371, hc13, hlam, hphi, u1ehi0]
                · linarith only [h2572, h3371, hc35, hlam, hphi, ht12, ht23, u1ehi0]
              · linarith only [h2572, h2580, h3370, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
            · linarith only [h0, h3369, hc25, hlam, hphi, ht12, u1ehi0]
          · linarith only [h0, h2578, h3368, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3377 | h3377
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3378 | h3378
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3379 | h3379
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3380 | h3380
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3381 | h3381
              · linarith only [h2572, h2580, h3381, hc13, hlam, hphi, u1ehi0]
              · linarith only [h2572, h3381, hc34, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h2579, h2580, h3377, h3380, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · linarith only [h0, h2578, h3379, hlam]
        · linarith only [h2580, h3377, h3378, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3387 | h3387
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3388 | h3388
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3389 | h3389
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3390 | h3390
              · linarith only [h2572, h2580, h3388, h3390, hc12, hlam, hphi, u1ehi0]
              · linarith only [h2572, h3390, hc34, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h0, h3389, hc25, hlam, hphi, ht12, u1ehi0]
          · linarith only [h0, h2578, h3388, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3395 | h3395
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3396 | h3396
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3397 | h3397
              · linarith only [h2572, h2580, h3395, h3397, hc12, hlam, hphi, u1ehi0]
              · linarith only [h2572, h3397, hc34, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h0, h2579, h3396, hlam]
          · linarith only [h0, h3395, hc23, hlam, hphi, ht12, u1ehi0]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3402 | h3402
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3403 | h3403
      · linarith only [h2578, h2579, h3403, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3405 | h3405
        · linarith only [h2578, h2579, h3402, h3405, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3407 | h3407
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3408 | h3408
            · linarith only [h0, h2579, h3408, hc12, hlam, hphi, u1ehi0]
            · linarith only [h0, h3408, hc25, hlam, hphi, ht12, u1ehi0]
          · linarith only [h0, h2578, h3407, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3412 | h3412
      · linarith only [h2578, h2579, h3412, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3414 | h3414
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3415 | h3415
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3416 | h3416
            · linarith only [h2572, h2578, h2579, h3416, hc12, hlam, hphi, u1ehi0]
            · linarith only [h0, h3416, hc25, hlam, hphi, ht12, u1ehi0]
          · linarith only [h0, h2578, h3415, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3420 | h3420
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3421 | h3421
            · linarith only [h0, h2579, h3421, hc12, hlam, hphi, u1ehi0]
            · linarith only [h0, h3421, hc25, hlam, hphi, ht12, u1ehi0]
          · linarith only [h0, h2578, h3420, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]

end R2N4
