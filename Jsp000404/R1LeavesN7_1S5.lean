import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8436000 in
set_option maxHeartbeats 8436000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2564 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2565 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2566 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h2567 | h2567
  · rcases m.htr 1 3 5 (by decide) (by decide) with h2568 | h2568
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2569 | h2569
      · linarith only [h2, h2569, h9, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2571 | h2571
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2572 | h2572
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2573 | h2573
            · linarith only [h2, h2565, h2573, h9, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2575 | h2575
              · linarith only [h2564, h2571, h2575, h9, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases h0bigk with h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [hlam, p2577_0]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [h0, h2564, h2572, hc01, hc35, hlam, hphi, ht0b, ht5b, p2577_1]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  rcases p2577_3 (m.d 0 1) (by simp) with h2580 | h2580
                  · rcases p2577_3 (m.d 0 2) (by simp) with h2581 | h2581
                    · linarith only [h0, h2581, hlam]
                    · linarith only [h2581, h4, hlam]
                  · linarith only [h1, h2580, hlam]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  rcases p2577_3 (m.d 0 1) (by simp) with h2585 | h2585
                  · rcases p2577_3 (m.d 0 2) (by simp) with h2586 | h2586
                    · linarith only [h0, h2586, hlam]
                    · linarith only [h2586, h5, hlam]
                  · linarith only [h2, h2585, hlam]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  rcases p2577_3 (m.d 0 1) (by simp) with h2590 | h2590
                  · rcases p2577_3 (m.d 0 2) (by simp) with h2591 | h2591
                    · linarith only [h0, h2591, hlam]
                    · linarith only [h2591, h6, hlam]
                  · linarith only [h2590, h3, hlam]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [h0, hlam, p2577_0]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [hlam, p2577_0]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  rcases p2577_3 (m.d 0 1) (by simp) with h2597 | h2597
                  · rcases p2577_3 (m.d 0 2) (by simp) with h2598 | h2598
                    · rcases p2577_3 (m.d 0 3) (by simp) with h2599 | h2599
                      · linarith only [h2599, h4, hlam]
                      · rcases p2577_3 (m.d 0 4) (by simp) with h2601 | h2601
                        · linarith only [h2601, h5, hlam]
                        · rcases p2577_3 (m.d 0 5) (by simp) with h2603 | h2603
                          · linarith only [h2603, h6, hlam]
                          · rcases h2bigk with h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c | h2605c
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h0, h2564, h2572, h2575, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2605_1]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              rcases p2605_3 (m.d 0 2) (by simp) with h2608 | h2608
                              · rcases p2605_3 (m.d 1 2) (by simp) with h2609 | h2609
                                · linarith only [h0, h2609, hlam]
                                · linarith only [h2564, h2609, hlam]
                              · linarith only [h2608, hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              rcases p2605_3 (m.d 0 2) (by simp) with h2613 | h2613
                              · rcases p2605_3 (m.d 1 2) (by simp) with h2614 | h2614
                                · linarith only [h0, h2614, hlam]
                                · linarith only [h2565, h2614, hlam]
                              · linarith only [h2613, hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              rcases p2605_3 (m.d 0 2) (by simp) with h2618 | h2618
                              · rcases p2605_3 (m.d 1 2) (by simp) with h2619 | h2619
                                · linarith only [h0, h2619, hlam]
                                · linarith only [h2566, h2619, hlam]
                              · linarith only [h2618, hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h0, hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h0, h2572, h2575, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2605_1]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              rcases p2605_3 (m.d 0 2) (by simp) with h2626 | h2626
                              · rcases p2605_3 (m.d 1 2) (by simp) with h2627 | h2627
                                · rcases p2605_3 (m.d 2 3) (by simp) with h2628 | h2628
                                  · linarith only [h2564, h2628, hlam]
                                  · linarith only [h2571, h2628, hlam]
                                · linarith only [h2627, hlam, p2605_0]
                              · linarith only [h2626, h5, hlam]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              rcases p2605_3 (m.d 0 2) (by simp) with h2633 | h2633
                              · rcases p2605_3 (m.d 1 2) (by simp) with h2634 | h2634
                                · rcases p2605_3 (m.d 2 3) (by simp) with h2635 | h2635
                                  · linarith only [h2564, h2635, hlam]
                                  · linarith only [h2572, h2635, hlam]
                                · linarith only [h2634, hlam, p2605_0]
                              · linarith only [h2633, h6, hlam]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h4, hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h2564, hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h1, h2564, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p2577_1, p2605_1]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h0, h1, h2564, hc01, hc25, hlam, hphi, ht0b, ht5b, p2577_1, p2605_1]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h5, hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h2565, hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h2571, hlam, p2605_1]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h2573, hlam, p2605_1]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h6, hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h2566, hlam, p2605_0]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h2572, hlam, p2605_1]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [h0, h2571, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2577_1, p2605_1]
                            · have p2605_0 := h2605c.1
                              have p2605_1 := h2605c.2.1
                              have p2605_2 := h2605c.2.2.1
                              have p2605_3 := h2605c.2.2.2
                              linarith only [hlam, p2605_0]
                    · linarith only [h2598, h4, hlam]
                  · linarith only [h1, h2597, hlam]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  rcases p2577_3 (m.d 0 1) (by simp) with h2657 | h2657
                  · rcases p2577_3 (m.d 0 2) (by simp) with h2658 | h2658
                    · rcases p2577_3 (m.d 0 3) (by simp) with h2659 | h2659
                      · linarith only [h2659, h4, hlam]
                      · linarith only [h2659, h7, hlam]
                    · linarith only [h2658, h5, hlam]
                  · linarith only [h2, h2657, hlam]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  rcases p2577_3 (m.d 0 1) (by simp) with h2664 | h2664
                  · rcases p2577_3 (m.d 0 2) (by simp) with h2665 | h2665
                    · rcases p2577_3 (m.d 0 3) (by simp) with h2666 | h2666
                      · linarith only [h2666, h4, hlam]
                      · linarith only [h2666, h8, hlam]
                    · linarith only [h2665, h6, hlam]
                  · linarith only [h2664, h3, hlam]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [h1, hlam, p2577_1]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [h4, hlam, p2577_1]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [hlam, p2577_0]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  rcases p2577_3 (m.d 0 1) (by simp) with h2674 | h2674
                  · rcases p2577_3 (m.d 0 2) (by simp) with h2675 | h2675
                    · rcases p2577_3 (m.d 0 3) (by simp) with h2676 | h2676
                      · rcases p2577_3 (m.d 0 4) (by simp) with h2677 | h2677
                        · linarith only [h2677, h7, hlam]
                        · rcases p2577_3 (m.d 0 5) (by simp) with h2679 | h2679
                          · linarith only [h2679, h8, hlam]
                          · linarith only [h2679, h9, hlam]
                      · linarith only [h2676, h7, hlam]
                    · linarith only [h2675, h5, hlam]
                  · linarith only [h2, h2674, hlam]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  rcases p2577_3 (m.d 0 1) (by simp) with h2685 | h2685
                  · rcases p2577_3 (m.d 0 2) (by simp) with h2686 | h2686
                    · rcases p2577_3 (m.d 0 3) (by simp) with h2687 | h2687
                      · rcases p2577_3 (m.d 0 4) (by simp) with h2688 | h2688
                        · linarith only [h2688, h7, hlam]
                        · rcases p2577_3 (m.d 0 5) (by simp) with h2690 | h2690
                          · linarith only [h2690, h8, hlam]
                          · rcases h2bigk with h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h0, h2564, h2571, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              rcases p2692_3 (m.d 0 2) (by simp) with h2695 | h2695
                              · rcases p2692_3 (m.d 1 2) (by simp) with h2696 | h2696
                                · linarith only [h0, h2696, hlam]
                                · linarith only [h2564, h2696, hlam]
                              · linarith only [h2695, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              rcases p2692_3 (m.d 0 2) (by simp) with h2700 | h2700
                              · rcases p2692_3 (m.d 1 2) (by simp) with h2701 | h2701
                                · linarith only [h0, h2701, hlam]
                                · linarith only [h2565, h2701, hlam]
                              · linarith only [h2700, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              rcases p2692_3 (m.d 0 2) (by simp) with h2705 | h2705
                              · rcases p2692_3 (m.d 1 2) (by simp) with h2706 | h2706
                                · linarith only [h0, h2706, hlam]
                                · linarith only [h2566, h2706, hlam]
                              · linarith only [h2705, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h0, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h0, h2572, h2575, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              rcases p2692_3 (m.d 0 2) (by simp) with h2713 | h2713
                              · rcases p2692_3 (m.d 1 2) (by simp) with h2714 | h2714
                                · rcases p2692_3 (m.d 2 3) (by simp) with h2715 | h2715
                                  · linarith only [h2564, h2715, hlam]
                                  · linarith only [h2571, h2715, hlam]
                                · linarith only [h2714, hlam, p2692_0]
                              · linarith only [h2713, h5, hlam]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              rcases p2692_3 (m.d 0 2) (by simp) with h2720 | h2720
                              · rcases p2692_3 (m.d 1 2) (by simp) with h2721 | h2721
                                · rcases p2692_3 (m.d 2 3) (by simp) with h2722 | h2722
                                  · linarith only [h2564, h2722, hlam]
                                  · linarith only [h2572, h2722, hlam]
                                · linarith only [h2721, hlam, p2692_0]
                              · linarith only [h2720, h6, hlam]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h4, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2564, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h0, h2564, h2571, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h0, h2564, hc01, hc25, hlam, hphi, ht0b, ht5b, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h5, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2565, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2571, hlam, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2573, hlam, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h6, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2566, hlam, p2692_0]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2572, hlam, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [h2571, h6, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2577_1, p2692_1]
                            · have p2692_0 := h2692c.1
                              have p2692_1 := h2692c.2.1
                              have p2692_2 := h2692c.2.2.1
                              have p2692_3 := h2692c.2.2.2
                              linarith only [hlam, p2692_0]
                      · linarith only [h2687, h8, hlam]
                    · linarith only [h2686, h6, hlam]
                  · linarith only [h2685, h3, hlam]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [h2, hlam, p2577_0]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [h5, hlam, p2577_0]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [h7, hlam, p2577_0]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [hlam, p2577_0]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [h9, hlam, p2577_0]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [h3, hlam, p2577_0]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [h6, hlam, p2577_1]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [h8, hlam, p2577_0]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  rcases p2577_3 (m.d 0 1) (by simp) with h2753 | h2753
                  · rcases p2577_3 (m.d 0 2) (by simp) with h2754 | h2754
                    · rcases p2577_3 (m.d 0 3) (by simp) with h2755 | h2755
                      · rcases p2577_3 (m.d 0 4) (by simp) with h2756 | h2756
                        · linarith only [h2756, h9, hlam]
                        · rcases p2577_3 (m.d 0 5) (by simp) with h2758 | h2758
                          · rcases h2bigk with h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h0, h2564, h2571, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              rcases p2759_3 (m.d 0 2) (by simp) with h2762 | h2762
                              · rcases p2759_3 (m.d 1 2) (by simp) with h2763 | h2763
                                · linarith only [h0, h2763, hlam]
                                · linarith only [h2564, h2763, hlam]
                              · linarith only [h2762, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              rcases p2759_3 (m.d 0 2) (by simp) with h2767 | h2767
                              · rcases p2759_3 (m.d 1 2) (by simp) with h2768 | h2768
                                · linarith only [h0, h2768, hlam]
                                · linarith only [h2565, h2768, hlam]
                              · linarith only [h2767, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              rcases p2759_3 (m.d 0 2) (by simp) with h2772 | h2772
                              · rcases p2759_3 (m.d 1 2) (by simp) with h2773 | h2773
                                · linarith only [h0, h2773, hlam]
                                · linarith only [h2566, h2773, hlam]
                              · linarith only [h2772, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h0, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h0, h2572, h2575, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              rcases p2759_3 (m.d 0 2) (by simp) with h2780 | h2780
                              · rcases p2759_3 (m.d 1 2) (by simp) with h2781 | h2781
                                · rcases p2759_3 (m.d 2 3) (by simp) with h2782 | h2782
                                  · linarith only [h2564, h2782, hlam]
                                  · linarith only [h2571, h2782, hlam]
                                · linarith only [h2781, hlam, p2759_0]
                              · linarith only [h2780, h5, hlam]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              rcases p2759_3 (m.d 0 2) (by simp) with h2787 | h2787
                              · rcases p2759_3 (m.d 1 2) (by simp) with h2788 | h2788
                                · rcases p2759_3 (m.d 2 3) (by simp) with h2789 | h2789
                                  · linarith only [h2564, h2789, hlam]
                                  · linarith only [h2572, h2789, hlam]
                                · linarith only [h2788, hlam, p2759_0]
                              · linarith only [h2787, h6, hlam]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h4, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2564, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h0, h2564, h2571, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h0, h2564, hc01, hc25, hlam, hphi, ht0b, ht5b, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h5, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2565, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2571, hlam, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2573, hlam, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h6, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2566, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2572, hlam, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h0, h2566, h2571, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [hlam, p2759_0]
                          · linarith only [h2758, h9, hlam]
                      · linarith only [h2755, h7, hlam]
                    · linarith only [h2754, h5, hlam]
                  · linarith only [h2, h2753, hlam]
                · have p2577_0 := h2577c.1
                  have p2577_1 := h2577c.2.1
                  have p2577_2 := h2577c.2.2.1
                  have p2577_3 := h2577c.2.2.2
                  linarith only [hlam, p2577_0]
          · linarith only [h0, h2564, h2568, h2571, h2572, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2815 | h2815
          · linarith only [h0, h2564, h2567, h2571, h2815, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2817 | h2817
            · linarith only [h2, h2567, h2571, h2817, h5, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2819 | h2819
              · linarith only [h2, h2567, h2819, h9, hlam]
              · rcases h0bigk with h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [hlam, p2821_0]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h0, h2564, h2568, h2571, h2819, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2821_1]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h1, h2568, h2571, h2819, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2821_1]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  rcases p2821_3 (m.d 0 1) (by simp) with h2825 | h2825
                  · rcases p2821_3 (m.d 0 2) (by simp) with h2826 | h2826
                    · linarith only [h0, h2826, hlam]
                    · linarith only [h2826, h5, hlam]
                  · linarith only [h2, h2825, hlam]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  rcases p2821_3 (m.d 0 1) (by simp) with h2830 | h2830
                  · rcases p2821_3 (m.d 0 2) (by simp) with h2831 | h2831
                    · linarith only [h0, h2831, hlam]
                    · linarith only [h2831, h6, hlam]
                  · linarith only [h2830, h3, hlam]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h0, hlam, p2821_0]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [hlam, p2821_0]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h1, h2568, h2571, h2819, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2821_1]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  rcases p2821_3 (m.d 0 1) (by simp) with h2838 | h2838
                  · rcases p2821_3 (m.d 0 2) (by simp) with h2839 | h2839
                    · rcases p2821_3 (m.d 0 3) (by simp) with h2840 | h2840
                      · linarith only [h2840, h4, hlam]
                      · linarith only [h2840, h7, hlam]
                    · linarith only [h2839, h5, hlam]
                  · linarith only [h2, h2838, hlam]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  rcases p2821_3 (m.d 0 1) (by simp) with h2845 | h2845
                  · rcases p2821_3 (m.d 0 2) (by simp) with h2846 | h2846
                    · rcases p2821_3 (m.d 0 3) (by simp) with h2847 | h2847
                      · linarith only [h2847, h4, hlam]
                      · linarith only [h2847, h8, hlam]
                    · linarith only [h2846, h6, hlam]
                  · linarith only [h2845, h3, hlam]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h1, hlam, p2821_1]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h4, hlam, p2821_1]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [hlam, p2821_0]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  rcases p2821_3 (m.d 0 1) (by simp) with h2855 | h2855
                  · rcases p2821_3 (m.d 0 2) (by simp) with h2856 | h2856
                    · rcases p2821_3 (m.d 0 3) (by simp) with h2857 | h2857
                      · rcases p2821_3 (m.d 0 4) (by simp) with h2858 | h2858
                        · linarith only [h2858, h7, hlam]
                        · rcases p2821_3 (m.d 0 5) (by simp) with h2860 | h2860
                          · linarith only [h2860, h8, hlam]
                          · linarith only [h2860, h9, hlam]
                      · linarith only [h2857, h7, hlam]
                    · linarith only [h2856, h5, hlam]
                  · linarith only [h2, h2855, hlam]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  rcases p2821_3 (m.d 0 1) (by simp) with h2866 | h2866
                  · rcases p2821_3 (m.d 0 2) (by simp) with h2867 | h2867
                    · rcases p2821_3 (m.d 0 3) (by simp) with h2868 | h2868
                      · rcases p2821_3 (m.d 0 4) (by simp) with h2869 | h2869
                        · linarith only [h2869, h7, hlam]
                        · rcases p2821_3 (m.d 0 5) (by simp) with h2871 | h2871
                          · linarith only [h2871, h8, hlam]
                          · rcases h2bigk with h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c | h2873c
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h0, h2564, h2568, h2571, h2819, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2571, h2819, h4, h8, hlam, p2821_1, p2873_2]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              rcases p2873_3 (m.d 0 2) (by simp) with h2877 | h2877
                              · rcases p2873_3 (m.d 1 2) (by simp) with h2878 | h2878
                                · linarith only [h0, h2878, hlam]
                                · linarith only [h2565, h2878, hlam]
                              · linarith only [h2877, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              rcases p2873_3 (m.d 0 2) (by simp) with h2882 | h2882
                              · rcases p2873_3 (m.d 1 2) (by simp) with h2883 | h2883
                                · linarith only [h0, h2883, hlam]
                                · linarith only [h2566, h2883, hlam]
                              · linarith only [h2882, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h0, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              rcases p2873_3 (m.d 0 2) (by simp) with h2889 | h2889
                              · rcases p2873_3 (m.d 1 2) (by simp) with h2890 | h2890
                                · rcases p2873_3 (m.d 2 3) (by simp) with h2891 | h2891
                                  · linarith only [h2891, hlam, p2873_0]
                                  · rcases p2873_3 (m.d 2 4) (by simp) with h2893 | h2893
                                    · linarith only [h2565, h2893, hlam]
                                    · linarith only [h2571, h2893, hlam]
                                · linarith only [h2890, hlam, p2873_0]
                              · linarith only [h2889, h4, hlam]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              rcases p2873_3 (m.d 0 2) (by simp) with h2898 | h2898
                              · rcases p2873_3 (m.d 1 2) (by simp) with h2899 | h2899
                                · rcases p2873_3 (m.d 2 3) (by simp) with h2900 | h2900
                                  · linarith only [h2564, h2900, hlam]
                                  · rcases p2873_3 (m.d 2 4) (by simp) with h2902 | h2902
                                    · linarith only [h2902, hlam, p2873_0]
                                    · rcases p2873_3 (m.d 2 5) (by simp) with h2904 | h2904
                                      · linarith only [h2566, h2904, hlam]
                                      · linarith only [h2817, h2904, hlam]
                                · linarith only [h2899, hlam, p2873_0]
                              · linarith only [h2898, h5, hlam]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              rcases p2873_3 (m.d 0 2) (by simp) with h2909 | h2909
                              · rcases p2873_3 (m.d 1 2) (by simp) with h2910 | h2910
                                · rcases p2873_3 (m.d 2 3) (by simp) with h2911 | h2911
                                  · linarith only [h2564, h2911, hlam]
                                  · rcases p2873_3 (m.d 2 4) (by simp) with h2913 | h2913
                                    · linarith only [h2565, h2913, hlam]
                                    · rcases p2873_3 (m.d 2 5) (by simp) with h2915 | h2915
                                      · linarith only [h2915, hlam, p2873_0]
                                      · rcases h3bigk with h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c | h2917c
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h2568, h2571, h2819, h4, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2917_1]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h2, h2567, h2571, h9, hlam, p2821_1, p2917_2]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          rcases p2917_3 (m.d 0 3) (by simp) with h2921 | h2921
                                          · rcases p2917_3 (m.d 1 3) (by simp) with h2922 | h2922
                                            · linarith only [h1, h2922, hlam]
                                            · linarith only [h2567, h2922, hlam]
                                          · linarith only [h2921, hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          rcases p2917_3 (m.d 0 3) (by simp) with h2926 | h2926
                                          · rcases p2917_3 (m.d 1 3) (by simp) with h2927 | h2927
                                            · linarith only [h1, h2927, hlam]
                                            · linarith only [h2568, h2927, hlam]
                                          · linarith only [h2926, hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h1, hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          rcases p2917_3 (m.d 0 3) (by simp) with h2933 | h2933
                                          · rcases p2917_3 (m.d 1 3) (by simp) with h2934 | h2934
                                            · rcases p2917_3 (m.d 2 3) (by simp) with h2935 | h2935
                                              · linarith only [h2564, h2935, hlam]
                                              · rcases p2917_3 (m.d 3 4) (by simp) with h2937 | h2937
                                                · linarith only [h2567, h2937, hlam]
                                                · linarith only [h2571, h2937, hlam]
                                            · linarith only [h2564, h2934, hlam]
                                          · linarith only [h2933, h4, hlam]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h1, h2571, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2917_1]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h0, h2564, h2571, h2819, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2917_1]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h4, hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h2564, hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h2571, hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h2815, hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h7, hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h2567, hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h2, h2567, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2821_1, p2917_1]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h2819, hlam, p2917_1]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h8, hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h2568, hlam, p2917_0]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2821_1, p2917_1]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [h0, h2568, h3, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2821_1, p2917_1]
                                        · have p2917_0 := h2917c.1
                                          have p2917_1 := h2917c.2.1
                                          have p2917_2 := h2917c.2.2.1
                                          have p2917_3 := h2917c.2.2.2
                                          linarith only [hlam, p2917_0]
                                · linarith only [h2910, hlam, p2873_0]
                              · linarith only [h2909, h6, hlam]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h4, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2564, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2571, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2815, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h5, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2565, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h0, h4, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2821_1, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2817, hlam, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h6, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h2566, hlam, p2873_0]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2821_1, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [h0, h2568, h2815, h3, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2821_1, p2873_1]
                            · have p2873_0 := h2873c.1
                              have p2873_1 := h2873c.2.1
                              have p2873_2 := h2873c.2.2.1
                              have p2873_3 := h2873c.2.2.2
                              linarith only [hlam, p2873_0]
                      · linarith only [h2868, h8, hlam]
                    · linarith only [h2867, h6, hlam]
                  · linarith only [h2866, h3, hlam]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h2, hlam, p2821_0]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h5, hlam, p2821_0]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h7, hlam, p2821_0]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [hlam, p2821_0]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h9, hlam, p2821_0]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h3, hlam, p2821_0]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h6, hlam, p2821_1]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h8, hlam, p2821_0]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [h2, h2567, h2571, h9, hc23, hc45, hlam, hphi, ht34, p2821_1]
                · have p2821_0 := h2821c.1
                  have p2821_1 := h2821c.2.1
                  have p2821_2 := h2821c.2.2.1
                  have p2821_3 := h2821c.2.2.2
                  linarith only [hlam, p2821_0]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2989 | h2989
      · linarith only [h2, h2567, h2568, h2989, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2991 | h2991
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2992 | h2992
          · linarith only [h2564, h2568, h2992, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2994 | h2994
            · linarith only [h2994, h5, h9, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2996 | h2996
              · linarith only [h2564, h2568, h2991, h2996, h8, h9, hlam]
              · rcases h0bigk with h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c | h2998c
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [hlam, p2998_0]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h2991, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2998_1]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h2564, h2568, h2991, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2998_1]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  rcases p2998_3 (m.d 0 1) (by simp) with h3002 | h3002
                  · rcases p2998_3 (m.d 0 2) (by simp) with h3003 | h3003
                    · linarith only [h0, h3003, hlam]
                    · linarith only [h3003, h5, hlam]
                  · linarith only [h2, h3002, hlam]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h2564, h2568, h2991, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2998_1]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h0, hlam, p2998_0]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [hlam, p2998_0]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h2564, h2568, h2991, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2998_1]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  rcases p2998_3 (m.d 0 1) (by simp) with h3011 | h3011
                  · rcases p2998_3 (m.d 0 2) (by simp) with h3012 | h3012
                    · rcases p2998_3 (m.d 0 3) (by simp) with h3013 | h3013
                      · linarith only [h3013, h4, hlam]
                      · linarith only [h3013, h7, hlam]
                    · linarith only [h3012, h5, hlam]
                  · linarith only [h2, h3011, hlam]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h0, h2564, h2568, h2991, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2998_1]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h1, hlam, p2998_1]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h4, hlam, p2998_1]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [hlam, p2998_0]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  rcases p2998_3 (m.d 0 1) (by simp) with h3022 | h3022
                  · rcases p2998_3 (m.d 0 2) (by simp) with h3023 | h3023
                    · rcases p2998_3 (m.d 0 3) (by simp) with h3024 | h3024
                      · rcases p2998_3 (m.d 0 4) (by simp) with h3025 | h3025
                        · linarith only [h3025, h7, hlam]
                        · rcases p2998_3 (m.d 0 5) (by simp) with h3027 | h3027
                          · linarith only [h3027, h8, hlam]
                          · linarith only [h3027, h9, hlam]
                      · linarith only [h3024, h7, hlam]
                    · linarith only [h3023, h5, hlam]
                  · linarith only [h2, h3022, hlam]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h2564, h2568, h2991, h8, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2998_1]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h2, hlam, p2998_0]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h5, hlam, p2998_0]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h7, hlam, p2998_0]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [hlam, p2998_0]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h9, hlam, p2998_0]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h3, hlam, p2998_0]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h6, hlam, p2998_1]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [h8, hlam, p2998_0]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  rcases p2998_3 (m.d 0 1) (by simp) with h3042 | h3042
                  · rcases p2998_3 (m.d 0 2) (by simp) with h3043 | h3043
                    · rcases p2998_3 (m.d 0 3) (by simp) with h3044 | h3044
                      · rcases p2998_3 (m.d 0 4) (by simp) with h3045 | h3045
                        · linarith only [h3045, h9, hlam]
                        · rcases p2998_3 (m.d 0 5) (by simp) with h3047 | h3047
                          · rcases h2bigk with h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c | h3048c
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h0, h2564, h2991, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              rcases p3048_3 (m.d 0 2) (by simp) with h3051 | h3051
                              · rcases p3048_3 (m.d 1 2) (by simp) with h3052 | h3052
                                · linarith only [h0, h3052, hlam]
                                · linarith only [h2564, h3052, hlam]
                              · linarith only [h3051, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              rcases p3048_3 (m.d 0 2) (by simp) with h3056 | h3056
                              · rcases p3048_3 (m.d 1 2) (by simp) with h3057 | h3057
                                · linarith only [h0, h3057, hlam]
                                · linarith only [h2565, h3057, hlam]
                              · linarith only [h3056, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              rcases p3048_3 (m.d 0 2) (by simp) with h3061 | h3061
                              · rcases p3048_3 (m.d 1 2) (by simp) with h3062 | h3062
                                · linarith only [h0, h3062, hlam]
                                · linarith only [h2566, h3062, hlam]
                              · linarith only [h3061, hlam, p3048_0]
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
                              linarith only [h0, h2991, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              rcases p3048_3 (m.d 0 2) (by simp) with h3069 | h3069
                              · rcases p3048_3 (m.d 1 2) (by simp) with h3070 | h3070
                                · rcases p3048_3 (m.d 2 3) (by simp) with h3071 | h3071
                                  · linarith only [h2564, h3071, hlam]
                                  · linarith only [h2991, h3071, hlam]
                                · linarith only [h3070, hlam, p3048_0]
                              · linarith only [h3069, h5, hlam]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h0, h2991, h2992, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h4, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2564, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2564, h2568, h4, h8, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2992, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h5, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2565, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2991, hlam, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2994, hlam, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h6, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h2566, hlam, p3048_0]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h0, h2566, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [h0, h2566, h2991, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3048_1]
                            · have p3048_0 := h3048c.1
                              have p3048_1 := h3048c.2.1
                              have p3048_2 := h3048c.2.2.1
                              have p3048_3 := h3048c.2.2.2
                              linarith only [hlam, p3048_0]
                          · linarith only [h3047, h9, hlam]
                      · linarith only [h3044, h7, hlam]
                    · linarith only [h3043, h5, hlam]
                  · linarith only [h2, h3042, hlam]
                · have p2998_0 := h2998c.1
                  have p2998_1 := h2998c.2.1
                  have p2998_2 := h2998c.2.2.1
                  have p2998_3 := h2998c.2.2.2
                  linarith only [hlam, p2998_0]
        · linarith only [h0, h2567, h2568, h2991, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h3098 | h3098
    · rcases m.htr 1 4 5 (by decide) (by decide) with h3099 | h3099
      · linarith only [h2567, h3098, h3099, h7, h9, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
      · linarith only [h2567, h3098, h3099, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h3102 | h3102
      · linarith only [h2, h3102, h9, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3104 | h3104
        · linarith only [h2564, h2567, h3104, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h3106 | h3106
          · linarith only [h2564, h3098, h3106, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h3108 | h3108
            · linarith only [h0, h2564, h2567, h3108, h5, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3110 | h3110
              · linarith only [h3110, h7, h9, hlam]
              · rcases h0bigk with h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c | h3112c
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [hlam, p3112_0]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h2564, h2567, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h2564, h2567, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  rcases p3112_3 (m.d 0 1) (by simp) with h3116 | h3116
                  · rcases p3112_3 (m.d 0 2) (by simp) with h3117 | h3117
                    · linarith only [h0, h3117, hlam]
                    · linarith only [h3117, h5, hlam]
                  · linarith only [h2, h3116, hlam]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  rcases p3112_3 (m.d 0 1) (by simp) with h3121 | h3121
                  · rcases p3112_3 (m.d 0 2) (by simp) with h3122 | h3122
                    · linarith only [h0, h3122, hlam]
                    · linarith only [h3122, h6, hlam]
                  · linarith only [h3, h3121, hlam]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h0, hlam, p3112_0]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [hlam, p3112_0]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h2564, h2567, h3110, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  rcases p3112_3 (m.d 0 1) (by simp) with h3129 | h3129
                  · rcases p3112_3 (m.d 0 2) (by simp) with h3130 | h3130
                    · rcases p3112_3 (m.d 0 3) (by simp) with h3131 | h3131
                      · linarith only [h3131, h4, hlam]
                      · linarith only [h3131, h7, hlam]
                    · linarith only [h3130, h5, hlam]
                  · linarith only [h2, h3129, hlam]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  rcases p3112_3 (m.d 0 1) (by simp) with h3136 | h3136
                  · rcases p3112_3 (m.d 0 2) (by simp) with h3137 | h3137
                    · rcases p3112_3 (m.d 0 3) (by simp) with h3138 | h3138
                      · linarith only [h3138, h4, hlam]
                      · linarith only [h3138, h8, hlam]
                    · linarith only [h3137, h6, hlam]
                  · linarith only [h3, h3136, hlam]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h1, hlam, p3112_1]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h4, hlam, p3112_1]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [hlam, p3112_0]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  rcases p3112_3 (m.d 0 1) (by simp) with h3146 | h3146
                  · rcases p3112_3 (m.d 0 2) (by simp) with h3147 | h3147
                    · rcases p3112_3 (m.d 0 3) (by simp) with h3148 | h3148
                      · rcases p3112_3 (m.d 0 4) (by simp) with h3149 | h3149
                        · linarith only [h3149, h7, hlam]
                        · rcases p3112_3 (m.d 0 5) (by simp) with h3151 | h3151
                          · linarith only [h3151, h8, hlam]
                          · linarith only [h3151, h9, hlam]
                      · linarith only [h3148, h7, hlam]
                    · linarith only [h3147, h5, hlam]
                  · linarith only [h2, h3146, hlam]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  rcases p3112_3 (m.d 0 1) (by simp) with h3157 | h3157
                  · rcases p3112_3 (m.d 0 2) (by simp) with h3158 | h3158
                    · rcases p3112_3 (m.d 0 3) (by simp) with h3159 | h3159
                      · rcases p3112_3 (m.d 0 4) (by simp) with h3160 | h3160
                        · linarith only [h3160, h7, hlam]
                        · rcases p3112_3 (m.d 0 5) (by simp) with h3162 | h3162
                          · linarith only [h3162, h8, hlam]
                          · rcases h2bigk with h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              rcases p3164_3 (m.d 0 2) (by simp) with h3166 | h3166
                              · rcases p3164_3 (m.d 1 2) (by simp) with h3167 | h3167
                                · linarith only [h0, h3167, hlam]
                                · rcases p3164_3 (m.d 2 3) (by simp) with h3169 | h3169
                                  · linarith only [h3169, h4, hlam]
                                  · rcases p3164_3 (m.d 2 4) (by simp) with h3171 | h3171
                                    · linarith only [h3171, h5, hlam]
                                    · rcases p3164_3 (m.d 2 5) (by simp) with h3173 | h3173
                                      · linarith only [h3173, h6, hlam]
                                      · rcases h3bigk with h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h2567, h3110, h8, hlam, p3112_1, p3175_2]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h2564, h2567, h3110, h8, hlam, p3112_1, p3175_2]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          rcases p3175_3 (m.d 0 3) (by simp) with h3179 | h3179
                                          · rcases p3175_3 (m.d 1 3) (by simp) with h3180 | h3180
                                            · linarith only [h1, h3180, hlam]
                                            · rcases p3175_3 (m.d 2 3) (by simp) with h3182 | h3182
                                              · linarith only [h3182, h4, hlam]
                                              · rcases p3175_3 (m.d 3 4) (by simp) with h3184 | h3184
                                                · linarith only [h3184, hlam, p3175_0]
                                                · rcases p3175_3 (m.d 3 5) (by simp) with h3186 | h3186
                                                  · linarith only [h3186, h8, hlam]
                                                  · linarith only [h3110, h3186, hlam]
                                          · linarith only [h3179, hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          rcases p3175_3 (m.d 0 3) (by simp) with h3190 | h3190
                                          · rcases p3175_3 (m.d 1 3) (by simp) with h3191 | h3191
                                            · linarith only [h1, h3191, hlam]
                                            · rcases p3175_3 (m.d 2 3) (by simp) with h3193 | h3193
                                              · linarith only [h3193, h4, hlam]
                                              · rcases p3175_3 (m.d 3 4) (by simp) with h3195 | h3195
                                                · linarith only [h3195, h7, hlam]
                                                · rcases p3175_3 (m.d 3 5) (by simp) with h3197 | h3197
                                                  · linarith only [h3197, hlam, p3175_0]
                                                  · rcases h5bigk with h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c | h3199c
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [hlam, p3199_0]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h2564, h2567, h3102, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h0, h3108, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3112_1, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h0, h2564, h2567, h3110, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h9, hlam, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h3, hlam, p3199_0]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [hlam, p3199_0]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h3, h3108, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h3098, hlam, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h3102, hlam, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h6, hlam, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h2566, hlam, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [hlam, p3199_0]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h3106, hlam, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h3108, hlam, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h8, hlam, p3199_0]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p3175_1, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h0, h3104, h3108, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [hlam, p3199_0]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h3110, hlam, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h2564, h2567, h3, h3102, hc23, hc45, hlam, hphi, ht34, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h2564, h2567, h3102, hc23, hc45, hlam, hphi, ht34, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h3104, h3108, hc23, hc45, hlam, hphi, ht34, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [h2564, h2567, h7, h9, hc23, hc45, hlam, hphi, ht34, p3112_1, p3175_2, p3199_1]
                                                    · have p3199_0 := h3199c.1
                                                      have p3199_1 := h3199c.2.1
                                                      have p3199_2 := h3199c.2.2.1
                                                      have p3199_3 := h3199c.2.2.2
                                                      linarith only [hlam, p3199_0]
                                          · linarith only [h3190, hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h1, hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h2567, hc23, hc34, hlam, hphi, p3175_1]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h2567, hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h3098, hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h4, hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h2564, hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h3104, hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h3106, hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h7, hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h0, h4, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3175_1]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h0, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3175_1]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h3110, hlam, p3175_1]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h8, hlam, p3175_0]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h0, h2564, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3175_1]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3175_1]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [h0, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3112_1, p3175_1]
                                        · have p3175_0 := h3175c.1
                                          have p3175_1 := h3175c.2.1
                                          have p3175_2 := h3175c.2.2.1
                                          have p3175_3 := h3175c.2.2.2
                                          linarith only [hlam, p3175_0]
                              · linarith only [h0, h3166, hlam]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h2564, h2567, h4, h7, h9, hlam, p3112_1, p3164_2]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              rcases p3164_3 (m.d 0 2) (by simp) with h3248 | h3248
                              · rcases p3164_3 (m.d 1 2) (by simp) with h3249 | h3249
                                · linarith only [h0, h3249, hlam]
                                · linarith only [h2565, h3249, hlam]
                              · linarith only [h3248, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              rcases p3164_3 (m.d 0 2) (by simp) with h3253 | h3253
                              · rcases p3164_3 (m.d 1 2) (by simp) with h3254 | h3254
                                · linarith only [h0, h3254, hlam]
                                · linarith only [h2566, h3254, hlam]
                              · linarith only [h3253, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h0, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              rcases p3164_3 (m.d 0 2) (by simp) with h3260 | h3260
                              · rcases p3164_3 (m.d 1 2) (by simp) with h3261 | h3261
                                · rcases p3164_3 (m.d 2 3) (by simp) with h3262 | h3262
                                  · linarith only [h3262, hlam, p3164_0]
                                  · rcases p3164_3 (m.d 2 4) (by simp) with h3264 | h3264
                                    · linarith only [h2565, h3264, hlam]
                                    · linarith only [h3104, h3264, hlam]
                                · linarith only [h3261, hlam, p3164_0]
                              · linarith only [h3260, h4, hlam]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              rcases p3164_3 (m.d 0 2) (by simp) with h3269 | h3269
                              · rcases p3164_3 (m.d 1 2) (by simp) with h3270 | h3270
                                · rcases p3164_3 (m.d 2 3) (by simp) with h3271 | h3271
                                  · linarith only [h2564, h3271, hlam]
                                  · rcases p3164_3 (m.d 2 4) (by simp) with h3273 | h3273
                                    · linarith only [h3273, hlam, p3164_0]
                                    · rcases p3164_3 (m.d 2 5) (by simp) with h3275 | h3275
                                      · linarith only [h2566, h3275, hlam]
                                      · linarith only [h3108, h3275, hlam]
                                · linarith only [h3270, hlam, p3164_0]
                              · linarith only [h3269, h5, hlam]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              rcases p3164_3 (m.d 0 2) (by simp) with h3280 | h3280
                              · rcases p3164_3 (m.d 1 2) (by simp) with h3281 | h3281
                                · rcases p3164_3 (m.d 2 3) (by simp) with h3282 | h3282
                                  · linarith only [h2564, h3282, hlam]
                                  · rcases p3164_3 (m.d 2 4) (by simp) with h3284 | h3284
                                    · linarith only [h2565, h3284, hlam]
                                    · rcases p3164_3 (m.d 2 5) (by simp) with h3286 | h3286
                                      · linarith only [h3286, hlam, p3164_0]
                                      · rcases h3bigk with h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h2567, h7, h9, hlam, p3112_1, p3288_2]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h2564, h2567, h7, h9, hlam, p3112_1, p3288_2]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          rcases p3288_3 (m.d 0 3) (by simp) with h3292 | h3292
                                          · rcases p3288_3 (m.d 1 3) (by simp) with h3293 | h3293
                                            · linarith only [h1, h3293, hlam]
                                            · rcases p3288_3 (m.d 2 3) (by simp) with h3295 | h3295
                                              · linarith only [h3295, h4, hlam]
                                              · rcases p3288_3 (m.d 3 4) (by simp) with h3297 | h3297
                                                · linarith only [h3297, hlam, p3288_0]
                                                · rcases p3288_3 (m.d 3 5) (by simp) with h3299 | h3299
                                                  · linarith only [h3299, h8, hlam]
                                                  · linarith only [h3110, h3299, hlam]
                                          · linarith only [h3292, hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          rcases p3288_3 (m.d 0 3) (by simp) with h3303 | h3303
                                          · rcases p3288_3 (m.d 1 3) (by simp) with h3304 | h3304
                                            · linarith only [h1, h3304, hlam]
                                            · rcases p3288_3 (m.d 2 3) (by simp) with h3306 | h3306
                                              · linarith only [h3306, h4, hlam]
                                              · rcases p3288_3 (m.d 3 4) (by simp) with h3308 | h3308
                                                · linarith only [h3308, h7, hlam]
                                                · rcases p3288_3 (m.d 3 5) (by simp) with h3310 | h3310
                                                  · linarith only [h3310, hlam, p3288_0]
                                                  · rcases h5bigk with h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [hlam, p3312_0]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h3102, h4, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p3112_1, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h0, h3108, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3112_1, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h0, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3112_1, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h9, hlam, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h3, hlam, p3312_0]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [hlam, p3312_0]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h3, h3108, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h3098, hlam, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h3102, hlam, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h6, hlam, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h2566, hlam, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [hlam, p3312_0]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h3106, hlam, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h3108, hlam, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h8, hlam, p3312_0]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p3288_1, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h0, h3104, h3108, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [hlam, p3312_0]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h3110, hlam, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h9, hc04, hc45, hlam, hphi, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h2564, h2567, h3102, hc23, hc45, hlam, hphi, ht34, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h3104, h3108, hc23, hc45, hlam, hphi, ht34, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [h2564, h2567, h7, h9, hc23, hc45, hlam, hphi, ht34, p3112_1, p3288_2, p3312_1]
                                                    · have p3312_0 := h3312c.1
                                                      have p3312_1 := h3312c.2.1
                                                      have p3312_2 := h3312c.2.2.1
                                                      have p3312_3 := h3312c.2.2.2
                                                      linarith only [hlam, p3312_0]
                                          · linarith only [h3303, hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h1, hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h0, h2567, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3288_1]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h2567, hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h3098, hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h4, hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h2564, hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h3104, hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h3106, hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h7, hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h0, h4, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3288_1]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h0, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3288_1]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h3110, hlam, p3288_1]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h8, hlam, p3288_0]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h0, h2564, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3288_1]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3288_1]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [h0, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3112_1, p3288_1]
                                        · have p3288_0 := h3288c.1
                                          have p3288_1 := h3288c.2.1
                                          have p3288_2 := h3288c.2.2.1
                                          have p3288_3 := h3288c.2.2.2
                                          linarith only [hlam, p3288_0]
                                · linarith only [h3281, hlam, p3164_0]
                              · linarith only [h3280, h6, hlam]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h4, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h2564, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h3104, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h3106, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h5, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h2565, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h0, h4, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h3108, hlam, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h6, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h2566, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3112_1, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h0, h2566, h3098, h4, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3112_1, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [hlam, p3164_0]
                      · linarith only [h3159, h8, hlam]
                    · linarith only [h3158, h6, hlam]
                  · linarith only [h3, h3157, hlam]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h2, hlam, p3112_0]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h5, hlam, p3112_0]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h7, hlam, p3112_0]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [hlam, p3112_0]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h9, hlam, p3112_0]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h3, hlam, p3112_0]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h6, hlam, p3112_1]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h8, hlam, p3112_0]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [h2564, h2567, h7, h9, hc23, hc45, hlam, hphi, ht34, p3112_1]
                · have p3112_0 := h3112c.1
                  have p3112_1 := h3112c.2.1
                  have p3112_2 := h3112c.2.2.1
                  have p3112_3 := h3112c.2.2.2
                  linarith only [hlam, p3112_0]

end R2N4
