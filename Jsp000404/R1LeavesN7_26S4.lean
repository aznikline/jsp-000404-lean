import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_26S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6256000 in
set_option maxHeartbeats 6256000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s1 m hb0 hb2 hb3 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2586 | h2586
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2587 | h2587
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2588 | h2588
        · linarith only [h0, h1, h2588, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2590 | h2590
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2591 | h2591
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2592 | h2592
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2593 | h2593
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2594 | h2594
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2595 | h2595
                    · linarith only [h0, h1, h2588, h2595, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2597 | h2597
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2598 | h2598
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2599 | h2599
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2600 | h2600
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2601 | h2601
                              · linarith only [h0, h1, h2595, h2597, h2601, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h1, h2595, h2601, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1, h2597, h2599, h2600, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h0, h1, h2599, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1, h2591, h2597, h2598, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h2590, h2595, h2597, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2608 | h2608
                    · linarith only [h0, h1, h2608, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2610 | h2610
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2611 | h2611
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2612 | h2612
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2613 | h2613
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2614 | h2614
                              · linarith only [h0, h1, h2608, h2610, h2614, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h1, h2608, h2610, h2612, h2614, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h1, h2610, h2612, h2613, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h0, h1, h2611, h2612, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h1, h2591, h2610, h2611, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h2590, h2608, h2610, hc12, hc23, hlam, hphi]
                · linarith only [h2592, h2593, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h2586, h2592, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2623 | h2623
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2624 | h2624
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2625 | h2625
                  · linarith only [h2590, h2591, h2625, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2627 | h2627
                    · linarith only [h0, h1, h2627, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2629 | h2629
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2630 | h2630
                        · linarith only [h0, h1, h2591, h2627, h2630, hc02, hc23, hlam, hphi]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2632 | h2632
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2633 | h2633
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2634 | h2634
                              · linarith only [h0, h1, h2627, h2629, h2634, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1, h2586, h2587, h2627, h2629, h2630, h2632, h2634, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h1, h2587, h2630, h2633, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h2587, h2630, h2632, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h2587, h2590, h2591, h2627, h2629, hc12, hc23, hlam, hphi]
                · linarith only [h2623, h2624, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h2586, h2623, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2642 | h2642
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2643 | h2643
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2644 | h2644
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2645 | h2645
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2646 | h2646
                    · linarith only [h0, h1, h2646, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2648 | h2648
                      · linarith only [h0, h1, h2590, h2646, h2648, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2650 | h2650
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2651 | h2651
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2652 | h2652
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2653 | h2653
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2654 | h2654
                                · linarith only [h0, h1, h2646, h2650, h2654, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                                · linarith only [h1, h2586, h2587, h2646, h2648, h2650, h2652, h2654, hc05, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h1, h2586, h2646, h2651, h2653, hlam]
                            · linarith only [h1, h2586, h2648, h2652, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h2586, h2648, h2651, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h1, h2586, h2590, h2642, h2646, h2650, hc12, hc23, hlam, hphi]
                  · linarith only [h2590, h2642, h2645, hlam]
                · linarith only [h2643, h2644, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h2586, h2643, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2664 | h2664
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2665 | h2665
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2666 | h2666
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2667 | h2667
                    · linarith only [h0, h2588, h2642, h2664, h2667, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2669 | h2669
                      · linarith only [h0, h1, h2590, h2669, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2671 | h2671
                        · linarith only [h0, h2642, h2671, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2673 | h2673
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2674 | h2674
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2675 | h2675
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2676 | h2676
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2677 | h2677
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2678 | h2678
                                    · rcases h0bigk with h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c | h2679c
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h1, h2667, hc02, hc23, hlam, hphi, p2679_1]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h1, hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h1, h2586, h2667, h2673, h2678, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2679_1, u3ehi4]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h0, h1, h2642, h2667, hc12, hc23, hlam, hphi, p2679_1]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h0, hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h2588, hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h2590, hlam, p2679_1]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h2642, hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h0, h1, h2667, hc12, hc23, hlam, hphi, p2679_1]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        rcases p2679_3 (m.d 0 1) (by simp) with h2691 | h2691
                                        · linarith only [h1, h2691, hlam]
                                        · linarith only [h0, h2691, hlam]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        rcases p2679_3 (m.d 0 1) (by simp) with h2695 | h2695
                                        · linarith only [h1, h2695, hlam]
                                        · linarith only [h2586, h2695, hlam]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        rcases p2679_3 (m.d 0 1) (by simp) with h2698 | h2698
                                        · linarith only [h1, h2698, hlam]
                                        · linarith only [h2587, h2698, hlam]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h2586, hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h0, h1, h2586, h2667, hc12, hc23, hlam, hphi, p2679_1]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h2664, hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h1, h2586, h2587, h2667, h2674, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2679_1, u3ehi4]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h2587, hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h0, h1, h2587, h2667, hc12, hc23, hlam, hphi, p2679_1]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h2665, hlam, p2679_0]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [h2666, hlam, p2679_1]
                                      · have p2679_0 := h2679c.1
                                        have p2679_1 := h2679c.2.1
                                        have p2679_2 := h2679c.2.2.1
                                        have p2679_3 := h2679c.2.2.2
                                        linarith only [hlam, p2679_0]
                                    · linarith only [h1, h2586, h2666, h2667, h2678, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h2590, h2666, h2677, hlam]
                                · linarith only [h0, h1, h2667, h2676, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h2586, h2667, h2673, h2675, hlam]
                            · linarith only [h1, h2586, h2673, h2674, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1, h2586, h2665, h2666, h2673, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2717 | h2717
                    · linarith only [h0, h1, h2717, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2719 | h2719
                      · linarith only [h0, h2590, h2719, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2721 | h2721
                        · linarith only [h0, h2642, h2721, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2723 | h2723
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2724 | h2724
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2725 | h2725
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2726 | h2726
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2727 | h2727
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2728 | h2728
                                    · linarith only [h2586, h2666, h2723, h2728, hlam]
                                    · rcases h0bigk with h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h1, h2717, hc02, hc23, hlam, hphi, p2730_1]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h1, hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h1, h2586, h2717, h2723, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2730_1, u3ehi3]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h1, h2586, h2666, h2717, h2723, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2730_1, u3ehi3]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h0, hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h2588, hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h2590, hlam, p2730_1]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h2642, hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h0, h1, h2717, hc12, hc23, hlam, hphi, p2730_1]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        rcases p2730_3 (m.d 0 1) (by simp) with h2742 | h2742
                                        · linarith only [h1, h2742, hlam]
                                        · linarith only [h0, h2742, hlam]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        rcases p2730_3 (m.d 0 1) (by simp) with h2746 | h2746
                                        · linarith only [h1, h2746, hlam]
                                        · linarith only [h2586, h2746, hlam]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        rcases p2730_3 (m.d 0 1) (by simp) with h2749 | h2749
                                        · linarith only [h1, h2749, hlam]
                                        · linarith only [h2587, h2749, hlam]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h2586, hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h0, h2666, h2727, hc12, hc24, hlam, hphi, p2730_1]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h2664, hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h2666, hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h2587, hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h0, h1, h2587, h2717, hc12, hc23, hlam, hphi, p2730_1]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h2665, hlam, p2730_0]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [h1, h2586, h2587, h2717, h2723, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2730_1, u3ehi3]
                                      · have p2730_0 := h2730c.1
                                        have p2730_1 := h2730c.2.1
                                        have p2730_2 := h2730c.2.2.1
                                        have p2730_3 := h2730c.2.2.2
                                        linarith only [hlam, p2730_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2762 | h2762
                                    · linarith only [h1, h2586, h2717, h2723, h2727, h2762, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases h0bigk with h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h0, h1, h2717, hc12, hc23, hlam, hphi, p2764_1]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h1, hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h0, h1, h2590, h2717, hc12, hc23, hlam, hphi, p2764_1]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h1, h2587, h2717, h2724, h2762, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2764_1, u3ehi3]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h0, hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h2588, hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h2590, hlam, p2764_1]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h2642, hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h0, h1, h2717, hc12, hc23, hlam, hphi, p2764_1]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        rcases p2764_3 (m.d 0 1) (by simp) with h2776 | h2776
                                        · linarith only [h1, h2776, hlam]
                                        · linarith only [h0, h2776, hlam]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        rcases p2764_3 (m.d 0 1) (by simp) with h2780 | h2780
                                        · linarith only [h1, h2780, hlam]
                                        · linarith only [h2586, h2780, hlam]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        rcases p2764_3 (m.d 0 1) (by simp) with h2783 | h2783
                                        · linarith only [h1, h2783, hlam]
                                        · linarith only [h2587, h2783, hlam]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h2586, hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h0, h1, h2586, h2717, hc12, hc23, hlam, hphi, p2764_1]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h2664, hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h2666, hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h2587, hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h0, h1, h2587, h2717, hc12, hc23, hlam, hphi, p2764_1]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h2665, hlam, p2764_0]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [h1, h2586, h2587, h2717, h2723, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2764_1, u3ehi3]
                                      · have p2764_0 := h2764c.1
                                        have p2764_1 := h2764c.2.1
                                        have p2764_2 := h2764c.2.2.1
                                        have p2764_3 := h2764c.2.2.2
                                        linarith only [hlam, p2764_0]
                                · linarith only [h0, h1, h2717, h2726, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h2587, h2717, h2724, h2725, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h1, h2586, h2723, h2724, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1, h2587, h2665, h2723, hc34, hlam, hphi, u3ehi4]
                · linarith only [h2664, h2665, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h2586, h2664, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2802 | h2802
        · linarith only [h0, h1, h2802, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2804 | h2804
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2805 | h2805
            · linarith only [h0, h2587, h2805, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2807 | h2807
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2808 | h2808
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2809 | h2809
                  · linarith only [h0, h2587, h2804, h2809, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2811 | h2811
                    · linarith only [h0, h1, h2802, h2811, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2813 | h2813
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2814 | h2814
                        · linarith only [h0, h2587, h2805, h2814, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2816 | h2816
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2817 | h2817
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2818 | h2818
                              · linarith only [h0, h2587, h2811, h2813, h2817, h2818, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h2586, h2587, h2811, h2813, h2816, h2817, h2818, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h1, h2808, h2813, h2816, h2817, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h1, h2813, h2816, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h2802, h2804, h2813, hc12, hc23, hlam, hphi]
                · linarith only [h2807, h2808, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h1, h2804, h2807, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2826 | h2826
            · linarith only [h2586, h2587, h2804, h2826, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2828 | h2828
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2829 | h2829
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2830 | h2830
                  · linarith only [h2586, h2587, h2830, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2832 | h2832
                    · linarith only [h0, h2587, h2802, h2832, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2834 | h2834
                      · linarith only [h0, h2804, h2834, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2836 | h2836
                        · linarith only [h0, h2587, h2826, h2836, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2838 | h2838
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2839 | h2839
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2840 | h2840
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2841 | h2841
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2842 | h2842
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2843 | h2843
                                    · linarith only [h2586, h2587, h2830, h2838, h2843, hlam]
                                    · rcases h0bigk with h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c | h2845c
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2587, h2830, h2840, h2842, hc02, hc23, hlam, hphi, p2845_1]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h1, hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2586, h2587, h2830, h2838, h2840, h2842, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2845_1, u3ehi3]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2587, hlam, p2845_1]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h0, hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2802, hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2804, hlam, p2845_1]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2826, hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h1, h2586, h2838, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2845_1, u3ehi3]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        rcases p2845_3 (m.d 0 1) (by simp) with h2857 | h2857
                                        · linarith only [h1, h2857, hlam]
                                        · linarith only [h0, h2857, hlam]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        rcases p2845_3 (m.d 0 1) (by simp) with h2861 | h2861
                                        · linarith only [h1, h2861, hlam]
                                        · linarith only [h2586, h2861, hlam]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h1, h2586, h2587, h2832, h2838, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2845_1, u3ehi3]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2586, hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h0, h1, h2586, h2832, hc12, hc23, hlam, hphi, p2845_1]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2828, hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2830, hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2586, h2838, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2845_1, u3ehi3]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h0, h2830, h2840, h2842, hc12, hc23, hlam, hphi, p2845_1]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2829, hlam, p2845_0]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [h2586, h2830, h2838, h2840, h2842, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2845_1, u3ehi3]
                                      · have p2845_0 := h2845c.1
                                        have p2845_1 := h2845c.2.1
                                        have p2845_2 := h2845c.2.2.1
                                        have p2845_3 := h2845c.2.2.2
                                        linarith only [hlam, p2845_0]
                                  · linarith only [h2586, h2587, h2836, h2838, h2842, hc45, hlam, hphi, ht34, u3ehi3]
                                · linarith only [h1, h2586, h2832, h2838, h2841, hc35, hlam, hphi, u3ehi3]
                              · linarith only [h2586, h2587, h2832, h2838, h2839, h2840, hlam]
                            · linarith only [h1, h2829, h2839, hlam]
                          · linarith only [h1, h2829, h2838, hc34, hlam, hphi, u3ehi4]
                · linarith only [h2828, h2829, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h2586, h2828, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2882 | h2882
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2883 | h2883
        · linarith only [h0, h1, h2883, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2885 | h2885
          · linarith only [h0, h2586, h2885, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2887 | h2887
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2888 | h2888
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2889 | h2889
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2890 | h2890
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2891 | h2891
                    · linarith only [h0, h1, h2883, h2887, h2891, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2893 | h2893
                      · linarith only [h0, h2586, h2885, h2893, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2895 | h2895
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2896 | h2896
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2897 | h2897
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2898 | h2898
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2899 | h2899
                                · linarith only [h0, h2586, h2895, h2899, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · linarith only [h0, h2586, h2882, h2891, h2895, h2896, h2897, h2899, hc05, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h1, h2888, h2891, h2898, hlam]
                            · linarith only [h0, h2586, h2896, h2897, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h2888, h2896, hlam]
                        · linarith only [h0, h2586, h2887, h2893, h2895, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2586, h2887, h2890, hlam]
                · linarith only [h2888, h2889, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2908 | h2908
                · linarith only [h2888, h2908, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h1, h2887, h2908, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2911 | h2911
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2912 | h2912
                · rcases m.htr 0 4 5 (by decide) (by decide) with h2913 | h2913
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h2914 | h2914
                    · linarith only [h0, h1, h2883, h2914, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h2916 | h2916
                      · linarith only [h0, h2885, h2916, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h2918 | h2918
                        · linarith only [h0, h2887, h2918, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h2920 | h2920
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h2921 | h2921
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2922 | h2922
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2923 | h2923
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2924 | h2924
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2925 | h2925
                                    · rcases h0bigk with h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c | h2926c
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [hlam, p2926_0]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h2586, h2914, h2920, hc02, hc23, hlam, hphi, p2926_1]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h1, hlam, p2926_0]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h2586, hlam, p2926_1]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h0, h2586, h2887, h2914, h2920, hc12, hc23, hlam, hphi, p2926_1]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h0, hlam, p2926_0]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [hlam, p2926_0]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h2883, hlam, p2926_0]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h2885, hlam, p2926_1]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h2887, hlam, p2926_0]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h0, h1, h2914, hc12, hc23, hlam, hphi, p2926_1]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        rcases p2926_3 (m.d 0 1) (by simp) with h2938 | h2938
                                        · linarith only [h1, h2938, hlam]
                                        · linarith only [h0, h2938, hlam]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [hlam, p2926_0]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h1, h2586, h2882, h2914, h2921, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2926_1, u3ehi4]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        rcases p2926_3 (m.d 0 1) (by simp) with h2943 | h2943
                                        · linarith only [h1, h2943, hlam]
                                        · linarith only [h2882, h2943, hlam]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h2882, h2921, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2926_1, u3ehi4]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        rcases p2926_3 (m.d 0 1) (by simp) with h2947 | h2947
                                        · linarith only [h2586, h2947, hlam]
                                        · linarith only [h0, h2947, hlam]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h2911, hlam, p2926_0]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [hlam, p2926_0]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        rcases p2926_3 (m.d 0 1) (by simp) with h2952 | h2952
                                        · linarith only [h2586, h2952, hlam]
                                        · linarith only [h2882, h2952, hlam]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h2882, hlam, p2926_0]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h0, h1, h2882, h2914, hc12, hc23, hlam, hphi, p2926_1]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h2912, hlam, p2926_0]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [h2913, hlam, p2926_1]
                                      · have p2926_0 := h2926c.1
                                        have p2926_1 := h2926c.2.1
                                        have p2926_2 := h2926c.2.2.1
                                        have p2926_3 := h2926c.2.2.2
                                        linarith only [hlam, p2926_0]
                                    · rcases h0bigk with h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c | h2960c
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [hlam, p2960_0]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h0, h2586, h2914, h2920, hc12, hc23, hlam, hphi, p2960_1]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h1, hlam, p2960_0]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h2586, hlam, p2960_1]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h2586, h2882, h2914, h2920, h2921, h2925, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2960_1, u3ehi3]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h0, hlam, p2960_0]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [hlam, p2960_0]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h2883, hlam, p2960_0]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h2885, hlam, p2960_1]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h2887, hlam, p2960_0]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h0, h1, h2914, hc12, hc23, hlam, hphi, p2960_1]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        rcases p2960_3 (m.d 0 1) (by simp) with h2972 | h2972
                                        · linarith only [h1, h2972, hlam]
                                        · linarith only [h0, h2972, hlam]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [hlam, p2960_0]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h1, h2586, h2882, h2914, h2921, h2925, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2960_1, u3ehi3]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h1, h2913, h2914, h2925, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2960_1, u3ehi3]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h2882, h2921, h2925, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2960_1, u3ehi3]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        rcases p2960_3 (m.d 0 1) (by simp) with h2979 | h2979
                                        · linarith only [h2586, h2979, hlam]
                                        · linarith only [h0, h2979, hlam]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h2911, hlam, p2960_0]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [hlam, p2960_0]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h2586, h2913, h2914, h2920, h2925, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2960_1, u3ehi3]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h2882, hlam, p2960_0]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h0, h1, h2882, h2914, hc12, hc23, hlam, hphi, p2960_1]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h2912, hlam, p2960_0]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [h2913, hlam, p2960_1]
                                      · have p2960_0 := h2960c.1
                                        have p2960_1 := h2960c.2.1
                                        have p2960_2 := h2960c.2.2.1
                                        have p2960_3 := h2960c.2.2.2
                                        linarith only [hlam, p2960_0]
                                  · linarith only [h0, h2586, h2916, h2924, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h2586, h2882, h2914, h2920, h2921, h2923, hlam]
                              · linarith only [h2586, h2882, h2914, h2920, h2921, h2922, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h2586, h2882, h2918, h2920, h2921, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h2882, h2911, h2918, h2920, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h2586, h2882, h2913, hlam]
                · linarith only [h2911, h2912, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h2997 | h2997
                · linarith only [h2911, h2997, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1, h2882, h2997, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3000 | h3000
        · linarith only [h0, h1, h3000, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3002 | h3002
          · linarith only [h0, h2586, h3002, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3004 | h3004
            · linarith only [h0, h2882, h3004, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3006 | h3006
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3007 | h3007
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3008 | h3008
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3009 | h3009
                    · linarith only [h0, h1, h3000, h3009, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3011 | h3011
                      · linarith only [h0, h2882, h3002, h3008, h3011, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3013 | h3013
                        · linarith only [h0, h2882, h3004, h3013, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3015 | h3015
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3016 | h3016
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3017 | h3017
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3018 | h3018
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3019 | h3019
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3020 | h3020
                                    · rcases h0bigk with h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c | h3021c
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [hlam, p3021_0]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h2882, h3013, h3017, h3019, hc02, hc23, hlam, hphi, p3021_1]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h1, hlam, p3021_0]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h2586, hlam, p3021_1]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h2882, hlam, p3021_1]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h0, hlam, p3021_0]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [hlam, p3021_0]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h3000, hlam, p3021_0]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h3002, hlam, p3021_1]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h3004, hlam, p3021_0]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h0, h3000, hc12, hc23, hlam, hphi, p3021_1]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        rcases p3021_3 (m.d 0 1) (by simp) with h3033 | h3033
                                        · linarith only [h1, h3033, hlam]
                                        · linarith only [h0, h3033, hlam]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [hlam, p3021_0]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h0, h1, h2586, h3009, hc12, hc23, hlam, hphi, p3021_1]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h0, h1, h2882, h3009, hc12, hc23, hlam, hphi, p3021_1]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h0, h3002, hc12, hc24, hlam, hphi, p3021_1]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        rcases p3021_3 (m.d 0 1) (by simp) with h3040 | h3040
                                        · linarith only [h2586, h3040, hlam]
                                        · linarith only [h0, h3040, hlam]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h3006, hlam, p3021_0]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [hlam, p3021_0]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h0, h1, h2882, h3006, h3009, hc12, hc23, hlam, hphi, p3021_1]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h0, h2882, h3013, hc12, hc25, hlam, hphi, p3021_1]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        rcases p3021_3 (m.d 0 1) (by simp) with h3047 | h3047
                                        · linarith only [h2882, h3047, hlam]
                                        · linarith only [h0, h3047, hlam]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h3007, hlam, p3021_0]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [h3008, hlam, p3021_1]
                                      · have p3021_0 := h3021c.1
                                        have p3021_1 := h3021c.2.1
                                        have p3021_2 := h3021c.2.2.1
                                        have p3021_3 := h3021c.2.2.2
                                        linarith only [hlam, p3021_0]
                                    · rcases h0bigk with h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [hlam, p3053_0]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h0, h1, h3009, hc12, hc23, hlam, hphi, p3053_1]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h1, hlam, p3053_0]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h2586, hlam, p3053_1]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h2882, hlam, p3053_1]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h0, hlam, p3053_0]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [hlam, p3053_0]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h3000, hlam, p3053_0]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h3002, hlam, p3053_1]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h3004, hlam, p3053_0]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h0, h1, h3009, hc12, hc23, hlam, hphi, p3053_1]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        rcases p3053_3 (m.d 0 1) (by simp) with h3065 | h3065
                                        · linarith only [h1, h3065, hlam]
                                        · linarith only [h0, h3065, hlam]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [hlam, p3053_0]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h1, h3008, h3009, h3020, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3053_1, u3ehi3]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h0, h1, h2882, h3009, hc12, hc23, hlam, hphi, p3053_1]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h0, h3002, h3017, hc12, hc23, hlam, hphi, p3053_1]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        rcases p3053_3 (m.d 0 1) (by simp) with h3072 | h3072
                                        · linarith only [h2586, h3072, hlam]
                                        · linarith only [h0, h3072, hlam]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h3006, hlam, p3053_0]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [hlam, p3053_0]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h1, h3006, h3008, h3009, h3020, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3053_1, u3ehi3]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h0, h2882, h3013, h3017, h3019, hc12, hc23, hlam, hphi, p3053_1]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        rcases p3053_3 (m.d 0 1) (by simp) with h3079 | h3079
                                        · linarith only [h2882, h3079, hlam]
                                        · linarith only [h0, h3079, hlam]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h3007, hlam, p3053_0]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [h3008, hlam, p3053_1]
                                      · have p3053_0 := h3053c.1
                                        have p3053_1 := h3053c.2.1
                                        have p3053_2 := h3053c.2.2.1
                                        have p3053_3 := h3053c.2.2.2
                                        linarith only [hlam, p3053_0]
                                  · linarith only [h3002, h3008, h3019, hlam]
                                · linarith only [h0, h1, h3009, h3018, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h2586, h3009, h3015, h3017, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h3007, h3016, hlam]
                          · linarith only [h1, h3006, h3015, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3090 | h3090
                    · linarith only [h0, h2586, h3090, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3092 | h3092
                      · linarith only [h0, h2586, h3008, h3092, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3094 | h3094
                        · linarith only [h0, h3004, h3094, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3096 | h3096
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3097 | h3097
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3098 | h3098
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3099 | h3099
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3100 | h3100
                                  · linarith only [h0, h2586, h3008, h3100, hc12, hc24, hlam, hphi]
                                  · linarith only [h0, h2586, h3092, h3100, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1, h3007, h3090, h3099, hlam]
                              · linarith only [h1, h3007, h3090, h3098, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h0, h2586, h3007, h3096, h3097, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h1, h3006, h3008, h3096, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h3006, h3007, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3108 | h3108
                · linarith only [h3006, h3108, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3110 | h3110
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3111 | h3111
                    · linarith only [h0, h1, h3111, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3113 | h3113
                      · linarith only [h0, h3002, h3113, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3115 | h3115
                        · linarith only [h0, h3004, h3115, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3117 | h3117
                          · linarith only [h0, h1, h3006, h3111, h3117, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h3117, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3120 | h3120
                    · linarith only [h0, h1, h3120, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3122 | h3122
                      · linarith only [h0, h1, h3006, h3110, h3122, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3124 | h3124
                        · linarith only [h0, h3004, h3124, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3126 | h3126
                          · linarith only [h0, h1, h3006, h3120, h3126, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h3126, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h3130 | h3130
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3131 | h3131
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3132 | h3132
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3133 | h3133
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3134 | h3134
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3135 | h3135
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3136 | h3136
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3137 | h3137
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3138 | h3138
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3139 | h3139
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3140 | h3140
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3141 | h3141
                        · linarith only [h0, h3129, h3141, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h3129, h3135, h3141, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h3129, h3135, h3140, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h3129, h3135, h3139, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h3129, h3135, h3138, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3147 | h3147
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3148 | h3148
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3149 | h3149
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3150 | h3150
                        · linarith only [h0, h3129, h3150, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h3129, h3135, h3147, h3150, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h3129, h3135, h3149, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h3129, h3135, h3148, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h3129, h3135, h3147, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h3135, h3136, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3157 | h3157
              · linarith only [h3135, h3157, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3159 | h3159
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3160 | h3160
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3161 | h3161
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3162 | h3162
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3163 | h3163
                        · linarith only [h0, h3129, h3135, h3163, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3165 | h3165
                          · linarith only [h0, h3129, h3165, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3167 | h3167
                            · linarith only [h3129, h3157, h3160, h3167, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3169 | h3169
                              · linarith only [h3129, h3157, h3160, h3169, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3171 | h3171
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3172 | h3172
                                  · rcases h0bigk with h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c | h3173c
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [hlam, p3173_0]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h0, hlam, p3173_1]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3173_1, u3ehi0]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h0, h3130, h3161, h3169, h3171, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3173_1, u3ehi2]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h0, h3134, h3169, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3173_1, u3ehi2]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h0, h3129, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3173_1, u3ehi1]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [hlam, p3173_0]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      rcases p3173_3 (m.d 0 1) (by simp) with h3181 | h3181
                                      · linarith only [h0, h3181, hlam]
                                      · linarith only [h3129, h3181, hlam]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      rcases p3173_3 (m.d 0 1) (by simp) with h3184 | h3184
                                      · linarith only [h0, h3184, hlam]
                                      · linarith only [h3130, h3184, hlam]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      rcases p3173_3 (m.d 0 1) (by simp) with h3187 | h3187
                                      · linarith only [h0, h3187, hlam]
                                      · linarith only [h3131, h3187, hlam]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h3129, hlam, p3173_1]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h3132, hlam, p3173_1]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [hlam, p3173_0]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h3135, hlam, p3173_1]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h3157, hlam, p3173_1]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h3130, hlam, p3173_0]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h3133, hlam, p3173_0]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h0, h3129, h3130, h3160, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3173_1, u3ehi2]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [hlam, p3173_0]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h3129, h3135, h3157, h3160, hc34, hlam, hphi, p3173_1, u3ehi2]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h3131, hlam, p3173_0]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h3134, hlam, p3173_1]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h0, h3129, h3131, h3160, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3173_1, u3ehi2]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [h3159, hlam, p3173_1]
                                    · have p3173_0 := h3173c.1
                                      have p3173_1 := h3173c.2.1
                                      have p3173_2 := h3173c.2.2.1
                                      have p3173_3 := h3173c.2.2.2
                                      linarith only [hlam, p3173_0]
                                  · linarith only [h0, h3130, h3161, h3171, h3172, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h3130, h3159, h3167, h3171, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h3129, h3160, h3162, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h3129, h3160, h3161, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h3129, h3160, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3210 | h3210
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3211 | h3211
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3212 | h3212
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3213 | h3213
                        · linarith only [h0, h3129, h3213, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3215 | h3215
                          · linarith only [h0, h3130, h3157, h3213, h3215, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3217 | h3217
                            · linarith only [h3129, h3135, h3210, h3217, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3219 | h3219
                              · linarith only [h3129, h3157, h3210, h3219, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3221 | h3221
                                · linarith only [h0, h3130, h3159, h3211, h3221, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3223 | h3223
                                  · linarith only [h3129, h3135, h3159, h3210, h3223, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h3129, h3135, h3210, h3223, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h3129, h3210, h3212, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h3129, h3210, h3211, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h3129, h3210, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h3131, h3134, hlam]
        · linarith only [h0, h3130, h3133, hlam]
      · linarith only [h0, h3129, h3132, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3232 | h3232
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3233 | h3233
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3234 | h3234
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3235 | h3235
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3236 | h3236
              · linarith only [h3129, h3131, h3236, hlam]
              · linarith only [h3235, h3236, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3239 | h3239
              · linarith only [h3235, h3239, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3241 | h3241
                · linarith only [h3130, h3131, h3241, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3243 | h3243
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3244 | h3244
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3245 | h3245
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3246 | h3246
                        · linarith only [h3129, h3131, h3245, h3246, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3248 | h3248
                          · linarith only [h3130, h3131, h3239, h3245, h3246, h3248, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h3129, h3131, h3243, h3248, hc35, hlam, hphi, u3ehi2]
                      · linarith only [h0, h3129, h3234, h3243, h3245, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h3129, h3243, h3244, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h3129, h3243, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3254 | h3254
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3255 | h3255
              · linarith only [h0, h3129, h3234, h3255, hlam]
              · linarith only [h3254, h3255, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3258 | h3258
              · linarith only [h3254, h3258, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3260 | h3260
                · linarith only [h0, h3130, h3234, h3260, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3262 | h3262
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3263 | h3263
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3264 | h3264
                      · linarith only [h0, h3129, h3234, h3262, h3264, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h3129, h3262, h3264, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h3129, h3262, h3263, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h3129, h3262, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h0, h3130, h3233, hlam]
      · linarith only [h0, h3129, h3232, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3271 | h3271
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3272 | h3272
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3273 | h3273
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3274 | h3274
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3275 | h3275
            · linarith only [h3129, h3130, h3275, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3277 | h3277
              · linarith only [h3275, h3277, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3279 | h3279
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3280 | h3280
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3281 | h3281
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3282 | h3282
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3283 | h3283
                        · linarith only [h3129, h3130, h3275, h3281, h3283, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h3129, h3130, h3280, h3283, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h3129, h3130, h3280, h3281, h3282, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h3273, h3281, hlam]
                  · linarith only [h0, h3129, h3280, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h3129, h3130, h3279, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h3271, h3274, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3291 | h3291
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3292 | h3292
            · linarith only [h0, h3129, h3273, h3292, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3294 | h3294
              · linarith only [h3292, h3294, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3296 | h3296
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3297 | h3297
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3298 | h3298
                    · linarith only [h0, h3129, h3273, h3297, h3298, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h3129, h3297, h3298, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h3129, h3297, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h3129, h3130, h3296, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h3271, h3291, hlam]
      · linarith only [h0, h3129, h3272, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3305 | h3305
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3306 | h3306
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3307 | h3307
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3308 | h3308
            · linarith only [h3129, h3130, h3308, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3310 | h3310
              · linarith only [h3308, h3310, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3312 | h3312
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3313 | h3313
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3314 | h3314
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3315 | h3315
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3316 | h3316
                        · linarith only [h3129, h3308, h3316, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h3129, h3130, h3313, h3316, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h0, h3307, h3315, hlam]
                    · linarith only [h0, h3306, h3314, hlam]
                  · linarith only [h0, h3129, h3313, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h3129, h3130, h3312, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3323 | h3323
            · linarith only [h3129, h3130, h3323, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3325 | h3325
              · linarith only [h3323, h3325, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3327 | h3327
                · linarith only [h3306, h3307, h3327, hlam]
                · linarith only [h3129, h3130, h3327, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3330 | h3330
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3331 | h3331
            · linarith only [h0, h3129, h3306, h3331, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3333 | h3333
              · linarith only [h3331, h3333, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3335 | h3335
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3336 | h3336
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3337 | h3337
                    · linarith only [h3129, h3271, h3306, h3330, h3336, h3337, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h3129, h3336, h3337, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h3129, h3336, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h3129, h3130, h3335, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3342 | h3342
            · linarith only [h0, h3129, h3306, h3342, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3344 | h3344
              · linarith only [h3342, h3344, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3346 | h3346
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3347 | h3347
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3348 | h3348
                    · linarith only [h0, h3129, h3306, h3347, h3348, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h3129, h3347, h3348, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h3129, h3347, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h3129, h3306, h3346, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h3129, h3305, hlam]

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h3355 | h3355
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3356 | h3356
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3357 | h3357
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3358 | h3358
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3359 | h3359
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3360 | h3360
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3361 | h3361
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3362 | h3362
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3363 | h3363
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3364 | h3364
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3365 | h3365
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3366 | h3366
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3367 | h3367
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3368 | h3368
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3369 | h3369
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3370 | h3370
                                · rcases h0bigk with h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c | h3371c
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [hlam, p3371_0]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h0, hlam, p3371_1]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3129, hlam, p3371_0]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3129, h3354, h3362, h3363, h3368, h3369, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3371_1, u3ehi4]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3129, h3358, h3362, h3368, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3371_1, u3ehi4]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h0, h3354, h3363, h3368, h3369, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3371_1, u3ehi4]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [hlam, p3371_0]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h0, h3129, h3354, h3363, h3368, h3369, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3371_1, u3ehi4]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    rcases p3371_3 (m.d 0 1) (by simp) with h3380 | h3380
                                    · linarith only [h0, h3380, hlam]
                                    · linarith only [h3354, h3380, hlam]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    rcases p3371_3 (m.d 0 1) (by simp) with h3383 | h3383
                                    · linarith only [h0, h3383, hlam]
                                    · linarith only [h3355, h3383, hlam]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3354, h3363, h3368, h3369, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p3371_1, u3ehi4]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3356, hlam, p3371_1]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [hlam, p3371_0]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    rcases p3371_3 (m.d 0 1) (by simp) with h3389 | h3389
                                    · linarith only [h3129, h3389, hlam]
                                    · linarith only [h3354, h3389, hlam]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    rcases p3371_3 (m.d 0 1) (by simp) with h3392 | h3392
                                    · linarith only [h3129, h3392, hlam]
                                    · linarith only [h3355, h3392, hlam]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3354, hlam, p3371_0]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3357, hlam, p3371_0]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3359, hlam, p3371_0]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [hlam, p3371_0]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h0, h3354, h3355, h3364, h3368, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3371_1, u3ehi4]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3355, hlam, p3371_0]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3358, hlam, p3371_1]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3360, hlam, p3371_0]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [h3361, hlam, p3371_1]
                                  · have p3371_0 := h3371c.1
                                    have p3371_1 := h3371c.2.1
                                    have p3371_2 := h3371c.2.2.1
                                    have p3371_3 := h3371c.2.2.2
                                    linarith only [hlam, p3371_0]
                                · linarith only [h3129, h3354, h3361, h3362, h3370, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h3129, h3354, h3361, h3362, h3367, h3369, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h3367, h3368, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h3129, h3354, h3362, h3365, h3367, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h3129, h3354, h3365, h3366, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h3129, h3354, h3359, h3365, hlam]
                    · linarith only [h0, h3358, h3364, hlam]
                  · linarith only [h0, h3357, h3363, hlam]
                · linarith only [h0, h3356, h3362, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3414 | h3414
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3415 | h3415
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3416 | h3416
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3417 | h3417
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3418 | h3418
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3419 | h3419
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3420 | h3420
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3421 | h3421
                              · linarith only [h3129, h3354, h3361, h3415, h3421, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3423 | h3423
                                · linarith only [h3129, h3355, h3361, h3414, h3416, h3419, h3421, h3423, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h0bigk with h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [hlam, p3425_0]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h0, hlam, p3425_1]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3129, hlam, p3425_0]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3129, h3354, h3414, h3415, h3419, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3425_1, u3ehi3]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3129, h3360, h3414, h3423, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3425_1, u3ehi3]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h0, h3354, h3415, h3419, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3425_1, u3ehi3]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [hlam, p3425_0]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h0, h3129, h3354, h3415, h3419, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3425_1, u3ehi3]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    rcases p3425_3 (m.d 0 1) (by simp) with h3434 | h3434
                                    · linarith only [h0, h3434, hlam]
                                    · linarith only [h3354, h3434, hlam]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    rcases p3425_3 (m.d 0 1) (by simp) with h3437 | h3437
                                    · linarith only [h0, h3437, hlam]
                                    · linarith only [h3355, h3437, hlam]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3355, h3416, h3420, h3423, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p3425_1, u3ehi3]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3356, hlam, p3425_1]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [hlam, p3425_0]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    rcases p3425_3 (m.d 0 1) (by simp) with h3443 | h3443
                                    · linarith only [h3129, h3443, hlam]
                                    · linarith only [h3354, h3443, hlam]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    rcases p3425_3 (m.d 0 1) (by simp) with h3446 | h3446
                                    · linarith only [h3129, h3446, hlam]
                                    · linarith only [h3355, h3446, hlam]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3354, hlam, p3425_0]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3357, hlam, p3425_0]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3359, hlam, p3425_0]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [hlam, p3425_0]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3361, hlam, p3425_0]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3355, hlam, p3425_0]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3358, hlam, p3425_1]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h3360, hlam, p3425_0]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [h0, h3354, h3355, h3415, h3419, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3425_1, u3ehi3]
                                  · have p3425_0 := h3425c.1
                                    have p3425_1 := h3425c.2.1
                                    have p3425_2 := h3425c.2.2.1
                                    have p3425_3 := h3425c.2.2.2
                                    linarith only [hlam, p3425_0]
                            · linarith only [h3129, h3355, h3414, h3418, h3420, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h3359, h3361, h3419, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h3129, h3354, h3417, h3418, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h3129, h3355, h3360, h3417, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h3358, h3416, hlam]
                  · linarith only [h0, h3357, h3415, hlam]
                · linarith only [h0, h3356, h3414, hlam]
            · linarith only [h3359, h3360, hc35, hlam, hphi, u3ehi3]
          · linarith only [h3129, h3354, h3359, hlam]
        · linarith only [h0, h3355, h3358, hlam]
      · linarith only [h3129, h3354, h3356, h3357, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3470 | h3470
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3471 | h3471
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3472 | h3472
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3473 | h3473
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3474 | h3474
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3475 | h3475
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3476 | h3476
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3477 | h3477
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3478 | h3478
                      · linarith only [h0, h3354, h3356, h3475, h3478, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h3354, h3356, h3472, h3475, h3478, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h3354, h3356, h3473, h3474, h3475, h3477, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h0, h3354, h3356, h3473, h3474, h3475, h3476, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3483 | h3483
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3484 | h3484
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3485 | h3485
                      · linarith only [h0, h3354, h3475, h3485, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h3129, h3472, h3485, hlam]
                    · linarith only [h0, h3354, h3471, h3473, h3474, h3484, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h0, h3470, h3483, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3490 | h3490
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3491 | h3491
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3492 | h3492
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3493 | h3493
                      · linarith only [h0, h3354, h3356, h3490, h3493, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h3356, h3472, h3490, h3493, hlam]
                    · linarith only [h0, h3356, h3490, h3492, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h3356, h3490, h3491, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3498 | h3498
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3499 | h3499
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3500 | h3500
                      · linarith only [h0, h3354, h3490, h3500, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h3129, h3472, h3474, h3500, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h0, h3471, h3499, hlam]
                  · linarith only [h0, h3470, h3498, hlam]
            · linarith only [h3472, h3473, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h3354, h3356, h3472, hlam]
        · linarith only [h0, h3355, h3471, hlam]
      · linarith only [h0, h3354, h3470, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3509 | h3509
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3510 | h3510
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3511 | h3511
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3512 | h3512
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3513 | h3513
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3514 | h3514
              · linarith only [h3354, h3355, h3514, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3516 | h3516
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3517 | h3517
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3518 | h3518
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3519 | h3519
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3520 | h3520
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3521 | h3521
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3522 | h3522
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3523 | h3523
                              · linarith only [h3354, h3355, h3514, h3516, h3517, h3520, h3523, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3525 | h3525
                                · linarith only [h3354, h3355, h3514, h3517, h3521, h3525, hlam]
                                · rcases h0bigk with h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c | h3527c
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [hlam, p3527_0]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h0, hlam, p3527_1]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3129, hlam, p3527_0]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3354, h3355, h3516, h3517, h3520, h3521, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3527_1, u3ehi3]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3355, hlam, p3527_1]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h0, h3354, h3517, h3521, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3527_1, u3ehi3]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [hlam, p3527_0]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h0, h3354, h3355, h3513, h3517, h3521, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3527_1, u3ehi3]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    rcases p3527_3 (m.d 0 1) (by simp) with h3536 | h3536
                                    · linarith only [h0, h3536, hlam]
                                    · linarith only [h3354, h3536, hlam]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h0, h3354, h3355, h3517, h3521, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3527_1, u3ehi3]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3354, h3517, h3521, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p3527_1, u3ehi3]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3509, hlam, p3527_1]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [hlam, p3527_0]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    rcases p3527_3 (m.d 0 1) (by simp) with h3543 | h3543
                                    · linarith only [h3129, h3543, hlam]
                                    · linarith only [h3354, h3543, hlam]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3129, h3354, h3355, h3516, h3517, h3521, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3527_1, u3ehi3]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3354, hlam, p3527_0]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3510, hlam, p3527_0]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3512, hlam, p3527_0]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [hlam, p3527_0]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3514, hlam, p3527_0]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3354, h3517, h3521, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p3527_1, u3ehi3]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3511, hlam, p3527_1]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3513, hlam, p3527_0]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [h3354, h3514, h3517, h3521, hc45, hlam, hphi, ht34, p3527_1, u3ehi3]
                                  · have p3527_0 := h3527c.1
                                    have p3527_1 := h3527c.2.1
                                    have p3527_2 := h3527c.2.2.1
                                    have p3527_3 := h3527c.2.2.2
                                    linarith only [hlam, p3527_0]
                            · linarith only [h3129, h3513, h3516, h3521, h3522, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h3512, h3514, h3521, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h3129, h3513, h3520, hlam]
                      · linarith only [h3129, h3513, h3519, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h3509, h3511, h3513, h3518, hlam]
                  · linarith only [h0, h3354, h3510, h3517, hlam]
                · linarith only [h0, h3509, h3516, hlam]
            · linarith only [h3512, h3513, hc35, hlam, hphi, u3ehi3]
          · linarith only [h3129, h3354, h3512, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3566 | h3566
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3567 | h3567
            · linarith only [h3509, h3511, h3567, hlam]
            · linarith only [h3566, h3567, hc35, hlam, hphi, u3ehi3]
          · linarith only [h3129, h3354, h3566, hlam]
      · linarith only [h0, h3354, h3510, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3572 | h3572
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3573 | h3573
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3574 | h3574
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3575 | h3575
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3576 | h3576
              · linarith only [h3354, h3355, h3576, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3578 | h3578
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3579 | h3579
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3580 | h3580
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3581 | h3581
                      · linarith only [h3354, h3355, h3509, h3573, h3578, h3581, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h3354, h3355, h3509, h3573, h3574, h3578, h3581, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h3509, h3573, h3578, h3580, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h3354, h3355, h3509, h3573, h3574, h3578, h3579, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3586 | h3586
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3587 | h3587
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3588 | h3588
                      · linarith only [h0, h3354, h3578, h3588, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h3129, h3575, h3588, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h3354, h3573, h3574, h3587, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h3572, h3586, hlam]
            · linarith only [h3574, h3575, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h3354, h3509, h3574, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3595 | h3595
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3596 | h3596
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3597 | h3597
              · linarith only [h0, h3354, h3573, h3597, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3599 | h3599
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3600 | h3600
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3601 | h3601
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3602 | h3602
                      · linarith only [h0, h3354, h3509, h3599, h3602, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h3354, h3509, h3595, h3599, h3602, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h3354, h3509, h3595, h3599, h3601, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h3354, h3509, h3595, h3599, h3600, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3607 | h3607
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3608 | h3608
                    · linarith only [h0, h3354, h3573, h3595, h3599, h3608, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3610 | h3610
                      · linarith only [h0, h3354, h3599, h3610, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h3129, h3595, h3610, hlam]
                  · linarith only [h0, h3354, h3572, h3595, h3607, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h3595, h3596, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h3354, h3509, h3595, hlam]
      · linarith only [h0, h3354, h3572, hlam]

end R2N4
