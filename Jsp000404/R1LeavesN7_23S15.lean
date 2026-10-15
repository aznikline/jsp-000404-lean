import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_12_24_L_I_M_IR_s0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_12_24_L_I_M_IR_s1 m hb2 hb4 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2590 | h2590
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2591 | h2591
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2592 | h2592
        · linarith only [h0, h1, h2592, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2594 | h2594
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2595 | h2595
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2596 | h2596
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2597 | h2597
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2598 | h2598
                  · linarith only [h2592, h2594, h2597, h2598, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2600 | h2600
                    · linarith only [h0, h1, h2600, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1, h2594, h2598, h2600, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2603 | h2603
                  · linarith only [h2592, h2594, h2603, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2605 | h2605
                    · linarith only [h0, h1, h2605, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1, h2594, h2603, h2605, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h2594, h2596, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2609 | h2609
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2610 | h2610
                · linarith only [h2594, h2595, h2610, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2612 | h2612
                  · linarith only [h0, h2592, h2594, h2612, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2614 | h2614
                    · linarith only [h0, h1, h2612, h2614, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h2594, h2595, h2614, hc12, hc25, hlam, hphi]
              · linarith only [h1, h2590, h2609, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2618 | h2618
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2619 | h2619
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2620 | h2620
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2621 | h2621
                  · linarith only [h0, h2592, h2619, h2621, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2623 | h2623
                    · linarith only [h0, h1, h2594, h2621, h2623, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2625 | h2625
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2626 | h2626
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2627 | h2627
                          · linarith only [h1, h2590, h2621, h2627, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h1, h2590, h2620, h2621, h2627, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                        · linarith only [h1, h2590, h2623, h2626, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h2594, h2618, h2625, hc12, hc24, hlam, hphi]
                · linarith only [h2594, h2618, h2620, hlam]
              · linarith only [h1, h2590, h2619, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2634 | h2634
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2635 | h2635
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2636 | h2636
                  · linarith only [h0, h1, h2592, h2636, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2638 | h2638
                    · linarith only [h0, h1, h2594, h2636, h2638, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2640 | h2640
                      · linarith only [h1, h2590, h2618, h2636, h2638, h2640, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2642 | h2642
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2643 | h2643
                          · linarith only [h1, h2590, h2636, h2643, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h1, h2590, h2635, h2636, h2642, h2643, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · linarith only [h1, h2590, h2635, h2642, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2647 | h2647
                  · linarith only [h0, h2592, h2647, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2649 | h2649
                    · linarith only [h0, h2594, h2649, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2651 | h2651
                      · linarith only [h0, h2618, h2651, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2653 | h2653
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2654 | h2654
                          · linarith only [h2590, h2635, h2654, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2656 | h2656
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2657 | h2657
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2658 | h2658
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2659 | h2659
                                  · linarith only [h2590, h2635, h2653, h2659, hlam]
                                  · rcases h2bigk with h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h0, h1, h2647, hc12, hc23, hlam, hphi, p2661_1]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2592, hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2594, hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2618, hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h0, hlam, p2661_1]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2647, hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2649, hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2651, hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      rcases p2661_3 (m.d 0 2) (by simp) with h2672 | h2672
                                      · linarith only [h2672, hlam, p2661_0]
                                      · rcases p2661_3 (m.d 1 2) (by simp) with h2674 | h2674
                                        · linarith only [h2647, h2674, hlam]
                                        · rcases p2661_3 (m.d 2 3) (by simp) with h2676 | h2676
                                          · rcases p2661_3 (m.d 2 4) (by simp) with h2677 | h2677
                                            · linarith only [h2656, h2677, hlam]
                                            · linarith only [h2594, h2677, hlam]
                                          · linarith only [h2676, hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      rcases p2661_3 (m.d 0 2) (by simp) with h2681 | h2681
                                      · linarith only [h2592, h2681, hlam]
                                      · linarith only [h0, h2681, hlam]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2594, h2635, h2658, hc02, hc23, hlam, hphi, p2661_1]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2590, h2635, h2653, h2658, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2661_1, u4ehi3]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      rcases p2661_3 (m.d 0 2) (by simp) with h2687 | h2687
                                      · linarith only [h2687, hlam, p2661_0]
                                      · rcases p2661_3 (m.d 1 2) (by simp) with h2689 | h2689
                                        · linarith only [h2649, h2689, hlam]
                                        · rcases p2661_3 (m.d 2 3) (by simp) with h2691 | h2691
                                          · rcases p2661_3 (m.d 2 4) (by simp) with h2692 | h2692
                                            · rcases p2661_3 (m.d 2 5) (by simp) with h2693 | h2693
                                              · linarith only [h2658, h2693, hlam]
                                              · linarith only [h2618, h2693, hlam]
                                            · linarith only [h2692, hlam, p2661_0]
                                          · linarith only [h2592, h2691, hlam]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      rcases p2661_3 (m.d 0 2) (by simp) with h2698 | h2698
                                      · linarith only [h2594, h2698, hlam]
                                      · linarith only [h0, h2698, hlam]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2656, hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2590, h2635, h2653, h2658, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2661_1, u4ehi3]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      rcases p2661_3 (m.d 0 2) (by simp) with h2704 | h2704
                                      · linarith only [h2704, hlam, p2661_0]
                                      · rcases p2661_3 (m.d 1 2) (by simp) with h2706 | h2706
                                        · linarith only [h2651, h2706, hlam]
                                        · rcases p2661_3 (m.d 2 3) (by simp) with h2708 | h2708
                                          · rcases p2661_3 (m.d 2 4) (by simp) with h2709 | h2709
                                            · rcases p2661_3 (m.d 2 5) (by simp) with h2710 | h2710
                                              · rcases h4bigk with h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2635, h2653, hc45, hlam, hphi, p2711_1, u4ehi3]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2594, hlam, p2711_1]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2635, hc45, hlam, hphi, p2711_1, u4ehi3]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2635, hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2590, hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2649, hlam, p2711_1]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h1, h2590, h2647, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2711_1, u4ehi3]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2654, hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  rcases p2711_3 (m.d 0 4) (by simp) with h2722 | h2722
                                                  · linarith only [h2594, h2722, hlam]
                                                  · rcases p2711_3 (m.d 1 4) (by simp) with h2724 | h2724
                                                    · linarith only [h2649, h2724, hlam]
                                                    · rcases p2711_3 (m.d 2 4) (by simp) with h2726 | h2726
                                                      · rcases p2711_3 (m.d 3 4) (by simp) with h2727 | h2727
                                                        · linarith only [h2656, h2727, hlam]
                                                        · rcases p2711_3 (m.d 4 5) (by simp) with h2729 | h2729
                                                          · linarith only [h2658, h2729, hlam]
                                                          · linarith only [h2635, h2729, hlam]
                                                      · linarith only [h2594, h2726, hlam]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  rcases p2711_3 (m.d 0 4) (by simp) with h2733 | h2733
                                                  · linarith only [h2594, h2733, hlam]
                                                  · linarith only [h2590, h2733, hlam]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  rcases p2711_3 (m.d 0 4) (by simp) with h2737 | h2737
                                                  · linarith only [h2594, h2737, hlam]
                                                  · linarith only [h2634, h2737, hlam]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2635, h2656, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2711_1, u4ehi0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2634, hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2653, hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2656, hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2659, hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2590, hc45, hlam, hphi, p2711_1, u4ehi1]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2653, hc45, hlam, hphi, p2711_1, u4ehi3]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2658, hlam, p2711_0]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [h2656, h2658, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2711_1, u4ehi3]
                                                · have p2711_0 := h2711c.1
                                                  have p2711_1 := h2711c.2.1
                                                  have p2711_2 := h2711c.2.2.1
                                                  have p2711_3 := h2711c.2.2.2
                                                  linarith only [hlam, p2711_0]
                                              · linarith only [h2710, hlam, p2661_0]
                                            · linarith only [h2594, h2709, hlam]
                                          · linarith only [h2592, h2708, hlam]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      rcases p2661_3 (m.d 0 2) (by simp) with h2754 | h2754
                                      · linarith only [h2618, h2754, hlam]
                                      · linarith only [h0, h2754, hlam]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2657, hlam, p2661_0]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [h2658, hlam, p2661_1]
                                    · have p2661_0 := h2661c.1
                                      have p2661_1 := h2661c.2.1
                                      have p2661_2 := h2661c.2.2.1
                                      have p2661_3 := h2661c.2.2.2
                                      linarith only [hlam, p2661_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2760 | h2760
                                  · linarith only [h1, h2590, h2647, h2653, h2658, h2760, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                                  · rcases h2bigk with h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c | h2762c
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h2594, hc12, hc24, hlam, hphi, p2762_1]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h2592, hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h2594, hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h2618, hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h0, hlam, p2762_1]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h2647, hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h2649, hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h2651, hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      rcases p2762_3 (m.d 0 2) (by simp) with h2773 | h2773
                                      · linarith only [h2773, hlam, p2762_0]
                                      · rcases p2762_3 (m.d 1 2) (by simp) with h2775 | h2775
                                        · linarith only [h2647, h2775, hlam]
                                        · rcases p2762_3 (m.d 2 3) (by simp) with h2777 | h2777
                                          · rcases p2762_3 (m.d 2 4) (by simp) with h2778 | h2778
                                            · linarith only [h2656, h2778, hlam]
                                            · linarith only [h2594, h2778, hlam]
                                          · linarith only [h2777, hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      rcases p2762_3 (m.d 0 2) (by simp) with h2782 | h2782
                                      · linarith only [h2592, h2782, hlam]
                                      · linarith only [h0, h2782, hlam]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h2594, hc02, hc23, hlam, hphi, p2762_1]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h0, h2618, hc12, hc23, hlam, hphi, p2762_1]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h0, h1, h2591, h2647, h2653, h2654, h2658, hc12, hc23, hc45, hlam, hphi, p2762_1, u4ehi3]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h1, h2591, h2647, h2653, h2654, h2658, hc12, hc23, hc45, hlam, hphi, p2762_1, u4ehi3]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h2656, hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h2658, hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      rcases p2762_3 (m.d 0 2) (by simp) with h2793 | h2793
                                      · linarith only [h2793, hlam, p2762_0]
                                      · rcases p2762_3 (m.d 1 2) (by simp) with h2795 | h2795
                                        · linarith only [h2651, h2795, hlam]
                                        · rcases p2762_3 (m.d 2 3) (by simp) with h2797 | h2797
                                          · rcases p2762_3 (m.d 2 4) (by simp) with h2798 | h2798
                                            · linarith only [h2658, h2798, hlam]
                                            · linarith only [h2594, h2798, hlam]
                                          · linarith only [h2592, h2797, hlam]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      rcases p2762_3 (m.d 0 2) (by simp) with h2802 | h2802
                                      · linarith only [h2618, h2802, hlam]
                                      · linarith only [h0, h2802, hlam]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h2657, hlam, p2762_0]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [h0, h2594, hc12, hc25, hlam, hphi, p2762_1]
                                    · have p2762_0 := h2762c.1
                                      have p2762_1 := h2762c.2.1
                                      have p2762_2 := h2762c.2.2.1
                                      have p2762_3 := h2762c.2.2.2
                                      linarith only [hlam, p2762_0]
                              · linarith only [h1, h2591, h2647, h2653, h2654, h2657, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                            · linarith only [h1, h2591, h2647, h2653, h2654, h2656, hlam]
                        · linarith only [h0, h1, h2653, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h2590, h2634, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2812 | h2812
        · linarith only [h0, h1, h2812, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2814 | h2814
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2815 | h2815
            · linarith only [h0, h2591, h2815, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2817 | h2817
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2818 | h2818
                · linarith only [h0, h2591, h2814, h2818, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2820 | h2820
                  · linarith only [h0, h1, h2812, h2820, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2822 | h2822
                    · linarith only [h0, h1, h2820, h2822, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1, h2814, h2820, h2822, hc12, hc23, hlam, hphi]
              · linarith only [h1, h2590, h2817, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2826 | h2826
            · linarith only [h2590, h2591, h2814, h2826, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2828 | h2828
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2829 | h2829
                · linarith only [h2590, h2591, h2829, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2831 | h2831
                  · linarith only [h0, h1, h2812, h2831, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2833 | h2833
                    · linarith only [h0, h2814, h2833, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2835 | h2835
                      · linarith only [h0, h2826, h2835, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2837 | h2837
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2838 | h2838
                          · linarith only [h1, h2590, h2831, h2838, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h2590, h2591, h2838, hc45, hlam, hphi, u4ehi1]
                        · linarith only [h1, h2590, h2837, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h1, h2590, h2828, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2843 | h2843
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2844 | h2844
        · linarith only [h0, h1, h2844, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2846 | h2846
          · linarith only [h0, h2590, h2846, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2848 | h2848
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2849 | h2849
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2850 | h2850
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2851 | h2851
                  · linarith only [h0, h1, h2844, h2848, h2851, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2853 | h2853
                    · linarith only [h0, h2590, h2846, h2853, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2855 | h2855
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2856 | h2856
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2857 | h2857
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2858 | h2858
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2859 | h2859
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2860 | h2860
                                · linarith only [h0, h2590, h2851, h2855, h2856, h2860, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                                · linarith only [h0, h2590, h2843, h2853, h2855, h2857, h2860, hc05, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h2590, h2851, h2855, h2856, h2857, h2859, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h2590, h2849, h2851, h2855, h2856, h2857, h2858, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h2590, h2855, h2857, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h0, h1, h2855, h2856, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h2590, h2848, h2853, h2855, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2590, h2848, h2850, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2869 | h2869
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2870 | h2870
                  · linarith only [h0, h2844, h2848, h2870, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2872 | h2872
                    · linarith only [h0, h1, h2872, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2874 | h2874
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2875 | h2875
                        · linarith only [h0, h1, h2849, h2870, h2875, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h2874, h2875, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h2590, h2848, h2872, h2874, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2843, h2849, h2869, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h2880 | h2880
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2881 | h2881
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2882 | h2882
                  · linarith only [h0, h1, h2844, h2882, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2884 | h2884
                    · linarith only [h0, h1, h2882, h2884, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2886 | h2886
                      · linarith only [h0, h2848, h2886, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2888 | h2888
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2889 | h2889
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2890 | h2890
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2891 | h2891
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2892 | h2892
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2893 | h2893
                                  · rcases h2bigk with h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c | h2894c
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2848, hc12, hc25, hlam, hphi, p2894_1]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2844, hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2846, hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2848, hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h0, hlam, p2894_1]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2882, hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2884, hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2886, hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      rcases p2894_3 (m.d 0 2) (by simp) with h2905 | h2905
                                      · linarith only [h2905, hlam, p2894_0]
                                      · rcases p2894_3 (m.d 1 2) (by simp) with h2907 | h2907
                                        · linarith only [h2882, h2907, hlam]
                                        · rcases p2894_3 (m.d 2 3) (by simp) with h2909 | h2909
                                          · rcases p2894_3 (m.d 2 4) (by simp) with h2910 | h2910
                                            · linarith only [h2890, h2910, hlam]
                                            · linarith only [h2846, h2910, hlam]
                                          · linarith only [h2909, hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      rcases p2894_3 (m.d 0 2) (by simp) with h2914 | h2914
                                      · linarith only [h2844, h2914, hlam]
                                      · linarith only [h0, h2914, hlam]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2590, h2884, hc01, hc23, hlam, hphi, ht12, p2894_1]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2848, hc02, hc23, hlam, hphi, p2894_1]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      rcases p2894_3 (m.d 0 2) (by simp) with h2920 | h2920
                                      · linarith only [h2920, hlam, p2894_0]
                                      · rcases p2894_3 (m.d 1 2) (by simp) with h2922 | h2922
                                        · linarith only [h2884, h2922, hlam]
                                        · rcases p2894_3 (m.d 2 3) (by simp) with h2924 | h2924
                                          · rcases p2894_3 (m.d 2 4) (by simp) with h2925 | h2925
                                            · rcases p2894_3 (m.d 2 5) (by simp) with h2926 | h2926
                                              · linarith only [h2892, h2926, hlam]
                                              · linarith only [h2848, h2926, hlam]
                                            · linarith only [h2925, hlam, p2894_0]
                                          · linarith only [h2844, h2924, hlam]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      rcases p2894_3 (m.d 0 2) (by simp) with h2931 | h2931
                                      · linarith only [h2846, h2931, hlam]
                                      · linarith only [h0, h2931, hlam]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2890, hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h0, h2848, hc12, hc24, hlam, hphi, p2894_1]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      rcases p2894_3 (m.d 0 2) (by simp) with h2937 | h2937
                                      · linarith only [h2937, hlam, p2894_0]
                                      · rcases p2894_3 (m.d 1 2) (by simp) with h2939 | h2939
                                        · linarith only [h2886, h2939, hlam]
                                        · rcases p2894_3 (m.d 2 3) (by simp) with h2941 | h2941
                                          · rcases p2894_3 (m.d 2 4) (by simp) with h2942 | h2942
                                            · rcases p2894_3 (m.d 2 5) (by simp) with h2943 | h2943
                                              · rcases h4bigk with h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c | h2944c
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2590, hlam, p2944_1]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2846, hlam, p2944_1]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h1, h2880, h2882, h2893, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2944_1, u4ehi4]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  rcases p2944_3 (m.d 0 4) (by simp) with h2949 | h2949
                                                  · rcases p2944_3 (m.d 1 4) (by simp) with h2950 | h2950
                                                    · rcases p2944_3 (m.d 2 4) (by simp) with h2951 | h2951
                                                      · rcases p2944_3 (m.d 3 4) (by simp) with h2952 | h2952
                                                        · linarith only [h2880, h2952, hlam]
                                                        · linarith only [h2893, h2952, hlam]
                                                      · linarith only [h2892, h2951, hlam]
                                                    · linarith only [h2889, h2950, hlam]
                                                  · linarith only [h2949, hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2590, h2843, h2884, h2889, h2890, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2944_1, u4ehi4]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2884, hlam, p2944_1]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2884, h2890, h2893, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2944_1, u4ehi4]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  rcases p2944_3 (m.d 0 4) (by simp) with h2962 | h2962
                                                  · linarith only [h2590, h2962, hlam]
                                                  · linarith only [h2881, h2962, hlam]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2590, h2843, h2889, h2890, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2944_1, u4ehi4]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2590, h2843, h2889, h2890, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2944_1, u4ehi4]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2890, h2893, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2944_1, u4ehi4]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  rcases p2944_3 (m.d 0 4) (by simp) with h2969 | h2969
                                                  · linarith only [h2846, h2969, hlam]
                                                  · linarith only [h2881, h2969, hlam]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2880, hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2888, hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2890, hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h1, h2880, h2882, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2944_1, u4ehi4]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2881, hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2889, hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2892, hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [h2893, hlam, p2944_0]
                                                · have p2944_0 := h2944c.1
                                                  have p2944_1 := h2944c.2.1
                                                  have p2944_2 := h2944c.2.2.1
                                                  have p2944_3 := h2944c.2.2.2
                                                  linarith only [hlam, p2944_0]
                                              · linarith only [h2943, hlam, p2894_0]
                                            · linarith only [h2846, h2942, hlam]
                                          · linarith only [h2844, h2941, hlam]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      rcases p2894_3 (m.d 0 2) (by simp) with h2985 | h2985
                                      · linarith only [h2848, h2985, hlam]
                                      · linarith only [h0, h2985, hlam]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2891, hlam, p2894_0]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [h2892, hlam, p2894_1]
                                    · have p2894_0 := h2894c.1
                                      have p2894_1 := h2894c.2.1
                                      have p2894_2 := h2894c.2.2.1
                                      have p2894_3 := h2894c.2.2.2
                                      linarith only [hlam, p2894_0]
                                  · linarith only [h2590, h2843, h2889, h2893, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h2590, h2843, h2884, h2889, h2892, hlam]
                              · linarith only [h2590, h2843, h2884, h2889, h2890, h2891, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h2590, h2843, h2882, h2888, h2889, h2890, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h2590, h2889, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h1, h2843, h2886, h2888, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h2590, h2843, h2881, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2998 | h2998
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2999 | h2999
                  · linarith only [h0, h1, h2880, h2999, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3001 | h3001
                    · linarith only [h0, h1, h3001, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3003 | h3003
                      · linarith only [h0, h2848, h3003, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3005 | h3005
                        · linarith only [h1, h2843, h2880, h2999, h3003, h3005, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h2843, h3003, h3005, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h2590, h2843, h2998, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3009 | h3009
        · linarith only [h0, h1, h3009, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3011 | h3011
          · linarith only [h0, h2590, h3011, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3013 | h3013
            · linarith only [h0, h2843, h3013, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3015 | h3015
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3016 | h3016
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3017 | h3017
                  · linarith only [h0, h1, h3009, h3017, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3019 | h3019
                    · linarith only [h0, h2843, h3011, h3016, h3019, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3021 | h3021
                      · linarith only [h0, h2843, h3013, h3021, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3023 | h3023
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3024 | h3024
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3025 | h3025
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3026 | h3026
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3027 | h3027
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3028 | h3028
                                  · rcases h2bigk with h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h0, h2843, h3017, h3023, h3024, hc12, hc23, hlam, hphi, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3009, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3011, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3013, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h0, hlam, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3017, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3019, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3021, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      rcases p3029_3 (m.d 0 2) (by simp) with h3040 | h3040
                                      · linarith only [h3040, hlam, p3029_0]
                                      · rcases p3029_3 (m.d 1 2) (by simp) with h3042 | h3042
                                        · linarith only [h3017, h3042, hlam]
                                        · rcases p3029_3 (m.d 2 3) (by simp) with h3044 | h3044
                                          · rcases p3029_3 (m.d 2 4) (by simp) with h3045 | h3045
                                            · linarith only [h3025, h3045, hlam]
                                            · linarith only [h3011, h3045, hlam]
                                          · linarith only [h3044, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      rcases p3029_3 (m.d 0 2) (by simp) with h3049 | h3049
                                      · linarith only [h3009, h3049, hlam]
                                      · linarith only [h0, h3049, hlam]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h2843, h3019, h3024, hc01, hc23, hlam, hphi, ht12, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h0, h2843, h3021, hc12, hc23, hlam, hphi, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      rcases p3029_3 (m.d 0 2) (by simp) with h3055 | h3055
                                      · linarith only [h3055, hlam, p3029_0]
                                      · rcases p3029_3 (m.d 1 2) (by simp) with h3057 | h3057
                                        · linarith only [h3019, h3057, hlam]
                                        · rcases p3029_3 (m.d 2 3) (by simp) with h3059 | h3059
                                          · rcases p3029_3 (m.d 2 4) (by simp) with h3060 | h3060
                                            · rcases p3029_3 (m.d 2 5) (by simp) with h3061 | h3061
                                              · linarith only [h3027, h3061, hlam]
                                              · linarith only [h3013, h3061, hlam]
                                            · linarith only [h3060, hlam, p3029_0]
                                          · linarith only [h3009, h3059, hlam]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      rcases p3029_3 (m.d 0 2) (by simp) with h3066 | h3066
                                      · linarith only [h3011, h3066, hlam]
                                      · linarith only [h0, h3066, hlam]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3025, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h0, h2843, h3021, h3025, hc12, hc23, hlam, hphi, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      rcases p3029_3 (m.d 0 2) (by simp) with h3072 | h3072
                                      · linarith only [h3072, hlam, p3029_0]
                                      · rcases p3029_3 (m.d 1 2) (by simp) with h3074 | h3074
                                        · linarith only [h3021, h3074, hlam]
                                        · rcases p3029_3 (m.d 2 3) (by simp) with h3076 | h3076
                                          · rcases p3029_3 (m.d 2 4) (by simp) with h3077 | h3077
                                            · rcases p3029_3 (m.d 2 5) (by simp) with h3078 | h3078
                                              · rcases h4bigk with h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c | h3079c
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h2590, hlam, p3079_1]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3011, hlam, p3079_1]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3028, hc04, hlam, hphi, ht0b, ht45, ht5b, p3079_1, u4ehi4]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  rcases p3079_3 (m.d 0 4) (by simp) with h3084 | h3084
                                                  · rcases p3079_3 (m.d 1 4) (by simp) with h3085 | h3085
                                                    · rcases p3079_3 (m.d 2 4) (by simp) with h3086 | h3086
                                                      · rcases p3079_3 (m.d 3 4) (by simp) with h3087 | h3087
                                                        · linarith only [h3015, h3087, hlam]
                                                        · linarith only [h3028, h3087, hlam]
                                                      · linarith only [h3027, h3086, hlam]
                                                    · linarith only [h3024, h3085, hlam]
                                                  · linarith only [h3084, hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3015, h3028, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3079_1, u4ehi4]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3019, hlam, p3079_1]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3017, h3023, h3028, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3079_1, u4ehi4]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  rcases p3079_3 (m.d 0 4) (by simp) with h3097 | h3097
                                                  · linarith only [h2590, h3097, hlam]
                                                  · linarith only [h3016, h3097, hlam]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3015, h3025, h3028, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3079_1, u4ehi4]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h0, h2590, h3025, hc12, hc23, hlam, hphi, p3079_1]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3025, h3028, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3079_1, u4ehi4]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  rcases p3079_3 (m.d 0 4) (by simp) with h3104 | h3104
                                                  · linarith only [h3011, h3104, hlam]
                                                  · linarith only [h3016, h3104, hlam]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3015, hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3023, hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3025, hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3015, hc03, hlam, hphi, ht0b, ht45, ht5b, p3079_1, u4ehi4]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3016, hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3024, hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3027, hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [h3028, hlam, p3079_0]
                                                · have p3079_0 := h3079c.1
                                                  have p3079_1 := h3079c.2.1
                                                  have p3079_2 := h3079c.2.2.1
                                                  have p3079_3 := h3079c.2.2.2
                                                  linarith only [hlam, p3079_0]
                                              · linarith only [h3078, hlam, p3029_0]
                                            · linarith only [h3011, h3077, hlam]
                                          · linarith only [h3009, h3076, hlam]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      rcases p3029_3 (m.d 0 2) (by simp) with h3120 | h3120
                                      · linarith only [h3013, h3120, hlam]
                                      · linarith only [h0, h3120, hlam]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3026, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3027, hlam, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [hlam, p3029_0]
                                  · rcases h2bigk with h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h0, h1, h3017, hc12, hc23, hlam, hphi, p3126_1]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h3009, hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h3011, hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h3013, hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h0, hlam, p3126_1]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h3017, hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h3019, hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h3021, hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      rcases p3126_3 (m.d 0 2) (by simp) with h3137 | h3137
                                      · linarith only [h3137, hlam, p3126_0]
                                      · rcases p3126_3 (m.d 1 2) (by simp) with h3139 | h3139
                                        · linarith only [h3017, h3139, hlam]
                                        · rcases p3126_3 (m.d 2 3) (by simp) with h3141 | h3141
                                          · rcases p3126_3 (m.d 2 4) (by simp) with h3142 | h3142
                                            · linarith only [h3025, h3142, hlam]
                                            · linarith only [h3011, h3142, hlam]
                                          · linarith only [h3141, hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      rcases p3126_3 (m.d 0 2) (by simp) with h3146 | h3146
                                      · linarith only [h3009, h3146, hlam]
                                      · linarith only [h0, h3146, hlam]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h2843, h3019, h3024, hc01, hc23, hlam, hphi, ht12, p3126_1]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h3013, hc02, hc23, hlam, hphi, p3126_1]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      rcases p3126_3 (m.d 0 2) (by simp) with h3152 | h3152
                                      · linarith only [h3152, hlam, p3126_0]
                                      · rcases p3126_3 (m.d 1 2) (by simp) with h3154 | h3154
                                        · linarith only [h3019, h3154, hlam]
                                        · rcases p3126_3 (m.d 2 3) (by simp) with h3156 | h3156
                                          · rcases p3126_3 (m.d 2 4) (by simp) with h3157 | h3157
                                            · rcases p3126_3 (m.d 2 5) (by simp) with h3158 | h3158
                                              · linarith only [h3027, h3158, hlam]
                                              · linarith only [h3013, h3158, hlam]
                                            · linarith only [h3157, hlam, p3126_0]
                                          · linarith only [h3009, h3156, hlam]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      rcases p3126_3 (m.d 0 2) (by simp) with h3163 | h3163
                                      · linarith only [h3011, h3163, hlam]
                                      · linarith only [h0, h3163, hlam]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h3025, hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h0, h2843, h3021, hc12, hc24, hlam, hphi, p3126_1]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      rcases p3126_3 (m.d 0 2) (by simp) with h3169 | h3169
                                      · linarith only [h3169, hlam, p3126_0]
                                      · rcases p3126_3 (m.d 1 2) (by simp) with h3171 | h3171
                                        · linarith only [h3021, h3171, hlam]
                                        · rcases p3126_3 (m.d 2 3) (by simp) with h3173 | h3173
                                          · rcases p3126_3 (m.d 2 4) (by simp) with h3174 | h3174
                                            · rcases p3126_3 (m.d 2 5) (by simp) with h3175 | h3175
                                              · rcases h4bigk with h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [hlam, p3176_0]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h2590, hlam, p3176_1]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3011, hlam, p3176_1]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  rcases p3176_3 (m.d 0 4) (by simp) with h3180 | h3180
                                                  · rcases p3176_3 (m.d 1 4) (by simp) with h3181 | h3181
                                                    · rcases p3176_3 (m.d 2 4) (by simp) with h3182 | h3182
                                                      · rcases p3176_3 (m.d 3 4) (by simp) with h3183 | h3183
                                                        · linarith only [h3015, h3183, hlam]
                                                        · rcases p3176_3 (m.d 4 5) (by simp) with h3185 | h3185
                                                          · linarith only [h3016, h3185, hlam]
                                                          · linarith only [h3028, h3185, hlam]
                                                      · linarith only [h3025, h3182, hlam]
                                                    · linarith only [h3023, h3181, hlam]
                                                  · linarith only [h3015, h3180, hlam]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h1, h3015, h3017, h3028, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3176_1, u4ehi3]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3016, h3028, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3176_1, u4ehi3]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [hlam, p3176_0]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3019, hlam, p3176_1]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  rcases p3176_3 (m.d 0 4) (by simp) with h3195 | h3195
                                                  · linarith only [h2590, h3195, hlam]
                                                  · linarith only [h3015, h3195, hlam]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3028, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3176_1, u4ehi3]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3016, h3028, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3176_1, u4ehi3]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h0, h2590, hc12, hc24, hlam, hphi, p3176_1]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [hlam, p3176_0]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  rcases p3176_3 (m.d 0 4) (by simp) with h3202 | h3202
                                                  · linarith only [h3011, h3202, hlam]
                                                  · linarith only [h3015, h3202, hlam]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3025, h3028, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3176_1, u4ehi3]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3015, hlam, p3176_0]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3023, hlam, p3176_0]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3025, hlam, p3176_0]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [hlam, p3176_0]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3028, hlam, p3176_0]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3016, hlam, p3176_0]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3024, hlam, p3176_0]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3027, hlam, p3176_0]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [h3015, h3016, hc03, hlam, hphi, ht0b, ht45, ht5b, p3176_1, u4ehi3]
                                                · have p3176_0 := h3176c.1
                                                  have p3176_1 := h3176c.2.1
                                                  have p3176_2 := h3176c.2.2.1
                                                  have p3176_3 := h3176c.2.2.2
                                                  linarith only [hlam, p3176_0]
                                              · linarith only [h3175, hlam, p3126_0]
                                            · linarith only [h3011, h3174, hlam]
                                          · linarith only [h3009, h3173, hlam]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      rcases p3126_3 (m.d 0 2) (by simp) with h3219 | h3219
                                      · linarith only [h3013, h3219, hlam]
                                      · linarith only [h0, h3219, hlam]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h3026, hlam, p3126_0]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [h3027, hlam, p3126_1]
                                    · have p3126_0 := h3126c.1
                                      have p3126_1 := h3126c.2.1
                                      have p3126_2 := h3126c.2.2.1
                                      have p3126_3 := h3126c.2.2.2
                                      linarith only [hlam, p3126_0]
                                · linarith only [h0, h1, h3011, h3015, h3016, h3017, h3027, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h1, h3017, h3026, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h3017, h3025, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h2590, h3015, h3016, h3024, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h3015, h3023, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3230 | h3230
                  · linarith only [h0, h2590, h3016, h3230, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3232 | h3232
                    · linarith only [h0, h2590, h3016, h3232, hc45, hlam, hphi, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3234 | h3234
                      · linarith only [h0, h3013, h3234, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3236 | h3236
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3237 | h3237
                          · linarith only [h0, h2590, h3016, h3232, h3237, hc12, hc24, hlam, hphi]
                          · linarith only [h0, h2590, h3237, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h1, h3015, h3236, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3241 | h3241
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3242 | h3242
                  · linarith only [h0, h1, h3015, h3242, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3244 | h3244
                    · linarith only [h0, h1, h3015, h3244, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3246 | h3246
                      · linarith only [h0, h3013, h3246, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3248 | h3248
                        · linarith only [h0, h1, h3015, h3242, h3248, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h3248, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3251 | h3251
                  · linarith only [h0, h2590, h3241, h3251, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3253 | h3253
                    · linarith only [h0, h1, h3015, h3241, h3253, hc45, hlam, hphi, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3255 | h3255
                      · linarith only [h0, h3013, h3255, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3257 | h3257
                        · linarith only [h0, h1, h3015, h3251, h3257, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h3257, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 1 5 (by decide) (by decide) with h4131 | h4131
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4132 | h4132
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4133 | h4133
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4134 | h4134
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4135 | h4135
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4136 | h4136
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4137 | h4137
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4138 | h4138
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4139 | h4139
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4140 | h4140
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4141 | h4141
                      · linarith only [h3260, h4130, h4141, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h3260, h4130, h4136, h4137, h4140, h4141, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h3260, h4130, h4136, h4140, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h3260, h4130, h4136, h4137, h4139, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h3260, h4130, h4136, h4137, h4138, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h0, h4130, h4132, h4136, h4137, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4148 | h4148
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4149 | h4149
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4150 | h4150
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4151 | h4151
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4152 | h4152
                      · linarith only [h3260, h4130, h4136, h4148, h4152, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4154 | h4154
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4155 | h4155
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4156 | h4156
                            · linarith only [h4130, h4136, h4149, h4156, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4158 | h4158
                              · linarith only [h4130, h4136, h4149, h4154, h4158, hlam]
                              · rcases h2bigk with h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c | h4160c
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h0, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h0, h4154, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4160_1, u4ehi3]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  rcases p4160_3 (m.d 0 2) (by simp) with h4164 | h4164
                                  · rcases p4160_3 (m.d 1 2) (by simp) with h4165 | h4165
                                    · rcases p4160_3 (m.d 2 3) (by simp) with h4166 | h4166
                                      · linarith only [h4132, h4166, hlam]
                                      · linarith only [h4154, h4166, hlam]
                                    · linarith only [h4149, h4165, hlam]
                                  · linarith only [h4164, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  rcases p4160_3 (m.d 0 2) (by simp) with h4171 | h4171
                                  · rcases p4160_3 (m.d 1 2) (by simp) with h4172 | h4172
                                    · rcases p4160_3 (m.d 2 3) (by simp) with h4173 | h4173
                                      · linarith only [h4132, h4173, hlam]
                                      · linarith only [h4155, h4173, hlam]
                                    · linarith only [h4150, h4172, hlam]
                                  · linarith only [h4171, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h3260, h4130, h4132, h4149, h4154, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4160_1, u4ehi3]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h4155, h4158, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4160_1, u4ehi3]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  rcases p4160_3 (m.d 0 2) (by simp) with h4181 | h4181
                                  · linarith only [h0, h4181, hlam]
                                  · linarith only [h4133, h4181, hlam]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  rcases p4160_3 (m.d 0 2) (by simp) with h4184 | h4184
                                  · linarith only [h0, h4184, hlam]
                                  · linarith only [h4134, h4184, hlam]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h4132, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h4148, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h4132, h4154, hc02, hlam, hphi, ht0b, ht45, ht5b, p4160_1, u4ehi3]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h0, h4132, h4155, h4158, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4160_1, u4ehi3]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h4133, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h4149, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h4154, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h4156, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h4134, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h4150, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h4155, hlam, p4160_0]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [h0, h4134, h4154, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4160_1, u4ehi3]
                                · have p4160_0 := h4160c.1
                                  have p4160_1 := h4160c.2.1
                                  have p4160_2 := h4160c.2.2.1
                                  have p4160_3 := h4160c.2.2.2
                                  linarith only [hlam, p4160_0]
                          · linarith only [h0, h4131, h4150, h4154, h4155, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4203 | h4203
                          · linarith only [h3260, h4130, h4148, h4151, h4154, h4203, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4205 | h4205
                            · linarith only [h3260, h4131, h4136, h4148, h4151, h4152, h4154, h4205, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4207 | h4207
                              · linarith only [h4130, h4136, h4151, h4207, hlam]
                              · rcases h2bigk with h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h0, hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  rcases p4209_3 (m.d 0 2) (by simp) with h4212 | h4212
                                  · rcases p4209_3 (m.d 1 2) (by simp) with h4213 | h4213
                                    · rcases p4209_3 (m.d 2 3) (by simp) with h4214 | h4214
                                      · linarith only [h4214, hlam, p4209_0]
                                      · rcases p4209_3 (m.d 2 4) (by simp) with h4216 | h4216
                                        · linarith only [h4133, h4216, hlam]
                                        · linarith only [h4154, h4216, hlam]
                                    · linarith only [h4148, h4213, hlam]
                                  · linarith only [h4212, hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  rcases p4209_3 (m.d 0 2) (by simp) with h4221 | h4221
                                  · rcases p4209_3 (m.d 1 2) (by simp) with h4222 | h4222
                                    · rcases p4209_3 (m.d 2 3) (by simp) with h4223 | h4223
                                      · linarith only [h4132, h4223, hlam]
                                      · rcases p4209_3 (m.d 2 4) (by simp) with h4225 | h4225
                                        · linarith only [h4225, hlam, p4209_0]
                                        · rcases p4209_3 (m.d 2 5) (by simp) with h4227 | h4227
                                          · linarith only [h4134, h4227, hlam]
                                          · linarith only [h4205, h4227, hlam]
                                    · linarith only [h4149, h4222, hlam]
                                  · linarith only [h4221, hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  rcases p4209_3 (m.d 0 2) (by simp) with h4232 | h4232
                                  · rcases p4209_3 (m.d 1 2) (by simp) with h4233 | h4233
                                    · rcases p4209_3 (m.d 2 3) (by simp) with h4234 | h4234
                                      · linarith only [h4132, h4234, hlam]
                                      · rcases p4209_3 (m.d 2 4) (by simp) with h4236 | h4236
                                        · linarith only [h4133, h4236, hlam]
                                        · rcases p4209_3 (m.d 2 5) (by simp) with h4238 | h4238
                                          · linarith only [h4238, hlam, p4209_0]
                                          · rcases h4bigk with h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c | h4240c
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4136, h4151, h4154, hc23, hc45, hlam, hphi, ht34, p4240_1]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4136, hc45, hlam, hphi, p4240_1, u4ehi2]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4136, h4154, hc23, hc45, hlam, hphi, ht34, p4240_1]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4136, hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4130, hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h3260, h4131, h4148, h4152, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4240_1, u4ehi2]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h3260, h4131, h4148, h4152, h4154, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4240_1]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4152, hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4133, hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4149, hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4154, hlam, p4240_1]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4205, hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4135, hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4151, hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4135, hc03, hlam, hphi, ht0b, ht45, ht5b, p4240_1, u4ehi2]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4207, hlam, p4240_0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [hc45, hlam, hphi, p4240_1, u4ehi0]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4149, hc45, hlam, hphi, p4240_1, u4ehi2]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [hc45, hlam, hphi, p4240_1, u4ehi2]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [h4154, hc23, hc45, hlam, hphi, ht34, p4240_1]
                                            · have p4240_0 := h4240c.1
                                              have p4240_1 := h4240c.2.1
                                              have p4240_2 := h4240c.2.2.1
                                              have p4240_3 := h4240c.2.2.2
                                              linarith only [hlam, p4240_0]
                                    · linarith only [h4150, h4233, hlam]
                                  · linarith only [h4232, hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h3260, h4130, h4132, h4151, h4154, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4209_1]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h0, h4130, h4151, h4154, hlam, p4209_2]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  rcases p4209_3 (m.d 0 2) (by simp) with h4271 | h4271
                                  · linarith only [h0, h4271, hlam]
                                  · linarith only [h4133, h4271, hlam]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  rcases p4209_3 (m.d 0 2) (by simp) with h4274 | h4274
                                  · linarith only [h0, h4274, hlam]
                                  · linarith only [h4134, h4274, hlam]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h4132, hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h4148, hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h4154, hlam, p4209_1]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h4203, hlam, p4209_1]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h4133, hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h4149, hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h4133, h4136, hc23, hc45, hlam, hphi, ht34, p4209_1]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h4205, hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h4134, hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h4150, hlam, p4209_0]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h3260, h4131, h4148, h4150, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4209_1]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [h3260, h4131, h4148, h4150, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4209_1, u4ehi2]
                                · have p4209_0 := h4209c.1
                                  have p4209_1 := h4209c.2.1
                                  have p4209_2 := h4209c.2.2.1
                                  have p4209_3 := h4209c.2.2.2
                                  linarith only [hlam, p4209_0]
                    · linarith only [h3260, h4130, h4151, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                  · linarith only [h3260, h4130, h4148, h4149, h4150, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · linarith only [h3260, h4130, h4148, h4149, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h4130, h4148, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h3260, h4130, h4135, hlam]
        · linarith only [h3260, h4131, h4132, h4134, hlam]
      · linarith only [h3260, h4130, h4132, h4133, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4299 | h4299
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4300 | h4300
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4301 | h4301
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4302 | h4302
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4303 | h4303
              · linarith only [h4132, h4299, h4303, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h0, h4130, h4302, h4303, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4306 | h4306
              · linarith only [h0, h4130, h4132, h4306, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h0, h4130, h4306, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h4130, h4132, h4301, hlam]
        · linarith only [h0, h4131, h4300, hlam]
      · linarith only [h0, h4130, h4299, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4312 | h4312
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4313 | h4313
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4314 | h4314
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4315 | h4315
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4316 | h4316
            · linarith only [h4130, h4131, h4316, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4318 | h4318
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4319 | h4319
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4320 | h4320
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4321 | h4321
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4322 | h4322
                      · linarith only [h3260, h4130, h4316, h4318, h4322, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · linarith only [h4130, h4131, h4322, hc45, hlam, hphi, u4ehi1]
                    · linarith only [h3260, h4130, h4319, h4321, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h4314, h4320, hlam]
                · linarith only [h3260, h4130, h4318, h4319, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h4312, h4318, hlam]
          · linarith only [h3260, h4130, h4315, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4330 | h4330
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4331 | h4331
            · linarith only [h0, h4130, h4314, h4331, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4333 | h4333
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4334 | h4334
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4335 | h4335
                  · linarith only [h3260, h4130, h4312, h4314, h4334, h4335, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h4130, h4334, h4335, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · linarith only [h3260, h4130, h4333, h4334, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h4130, h4312, h4333, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
          · linarith only [h3260, h4130, h4330, hlam]
      · linarith only [h0, h4130, h4313, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4342 | h4342
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4343 | h4343
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4344 | h4344
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4345 | h4345
            · linarith only [h4130, h4131, h4345, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4347 | h4347
              · linarith only [h4312, h4342, h4347, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h0, h4130, h4347, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h4130, h4131, h4312, h4343, h4344, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4351 | h4351
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4352 | h4352
            · linarith only [h0, h4130, h4343, h4352, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4354 | h4354
              · linarith only [h0, h4130, h4312, h4354, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h0, h4130, h4354, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h4130, h4312, h4351, hlam]
      · linarith only [h0, h4130, h4342, hlam]

end R2N4
