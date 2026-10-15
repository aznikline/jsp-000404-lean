import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6446000 in
set_option maxHeartbeats 6446000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s3 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2562 | h2562
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2563 | h2563
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2564 | h2564
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2565 | h2565
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2566 | h2566
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2567 | h2567
              · linarith only [h0, h2567, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2569 | h2569
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2570 | h2570
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2571 | h2571
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2572 | h2572
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2573 | h2573
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2574 | h2574
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2575 | h2575
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2576 | h2576
                              · linarith only [h0, h2569, h2576, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2578 | h2578
                                · linarith only [h2574, h2576, h2578, hlam]
                                · rcases h2bigk with h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c | h2580c
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h4, hc12, hc23, hlam, hphi, p2580_1]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h4, hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    rcases p2580_3 (m.d 0 2) (by simp) with h2584 | h2584
                                    · rcases p2580_3 (m.d 1 2) (by simp) with h2585 | h2585
                                      · linarith only [h0, h2585, hlam]
                                      · linarith only [h2569, h2585, hlam]
                                    · linarith only [h2584, hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2580_1, u5ehi2]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h0, hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h2567, hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    rcases p2580_3 (m.d 0 2) (by simp) with h2593 | h2593
                                    · rcases p2580_3 (m.d 1 2) (by simp) with h2594 | h2594
                                      · rcases p2580_3 (m.d 2 3) (by simp) with h2595 | h2595
                                        · rcases p2580_3 (m.d 2 4) (by simp) with h2596 | h2596
                                          · linarith only [h2596, hlam, p2580_0]
                                          · rcases p2580_3 (m.d 2 5) (by simp) with h2598 | h2598
                                            · linarith only [h2570, h2598, hlam]
                                            · linarith only [h2576, h2598, hlam]
                                        · linarith only [h2574, h2595, hlam]
                                      · linarith only [h2594, hlam, p2580_0]
                                    · linarith only [h2562, h2593, hlam]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h0, h2575, hc01, hlam, hphi, ht0b, ht5b, p2580_1, u5ehi3]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p2580_1, u0ehi1]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h2569, h2573, h2574, h2576, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2580_1]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h2, h2562, h2573, h2576, h4, hlam, p2580_2]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    rcases p2580_3 (m.d 0 2) (by simp) with h2609 | h2609
                                    · linarith only [h2609, h4, hlam]
                                    · linarith only [h2563, h2609, hlam]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h2562, hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h2569, hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h2574, hlam, p2580_1]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h2576, hlam, p2580_1]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h2563, hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h2570, hlam, p2580_0]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h2575, hlam, p2580_1]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [h2563, h2574, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2580_1]
                                  · have p2580_0 := h2580c.1
                                    have p2580_1 := h2580c.2.1
                                    have p2580_2 := h2580c.2.2.1
                                    have p2580_3 := h2580c.2.2.2
                                    linarith only [hlam, p2580_0]
                            · linarith only [h2575, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h0, h2570, h2574, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2624 | h2624
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2625 | h2625
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2626 | h2626
                              · linarith only [h2569, h2573, h2626, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2628 | h2628
                                · linarith only [h2569, h2573, h2624, h2628, hlam]
                                · rcases h2bigk with h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2570, h2625, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2630_1, u5ehi3]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h4, hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    rcases p2630_3 (m.d 0 2) (by simp) with h2634 | h2634
                                    · rcases p2630_3 (m.d 1 2) (by simp) with h2635 | h2635
                                      · linarith only [h0, h2635, hlam]
                                      · linarith only [h2569, h2635, hlam]
                                    · linarith only [h2634, hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2625, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2630_1, u5ehi3]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h0, hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2567, hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    rcases p2630_3 (m.d 0 2) (by simp) with h2643 | h2643
                                    · rcases p2630_3 (m.d 1 2) (by simp) with h2644 | h2644
                                      · rcases p2630_3 (m.d 2 3) (by simp) with h2645 | h2645
                                        · rcases p2630_3 (m.d 2 4) (by simp) with h2646 | h2646
                                          · linarith only [h2646, hlam, p2630_0]
                                          · rcases p2630_3 (m.d 2 5) (by simp) with h2648 | h2648
                                            · linarith only [h2570, h2648, hlam]
                                            · linarith only [h2626, h2648, hlam]
                                        · linarith only [h2624, h2645, hlam]
                                      · linarith only [h2644, hlam, p2630_0]
                                    · linarith only [h2562, h2643, hlam]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h0, h2625, hc01, hlam, hphi, ht0b, ht5b, p2630_1, u5ehi3]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2562, h2566, h2573, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2630_1]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2570, h2625, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2630_1, u5ehi3]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2562, h2566, h2569, h2573, h4, hlam, p2630_2]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    rcases p2630_3 (m.d 0 2) (by simp) with h2659 | h2659
                                    · linarith only [h2659, h4, hlam]
                                    · linarith only [h2563, h2659, hlam]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2562, hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2569, hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2624, hlam, p2630_1]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2626, hlam, p2630_1]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2563, hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2570, hlam, p2630_0]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2625, hlam, p2630_1]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [h2562, h2566, h2570, h2573, h2624, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2630_1]
                                  · have p2630_0 := h2630c.1
                                    have p2630_1 := h2630c.2.1
                                    have p2630_2 := h2630c.2.2.1
                                    have p2630_3 := h2630c.2.2.2
                                    linarith only [hlam, p2630_0]
                            · linarith only [h2562, h2566, h2572, h2573, h2625, h4, hlam]
                          · linarith only [h2562, h2566, h2573, h2624, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h2565, h2567, h2570, h2572, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · linarith only [h2564, h2567, h2570, h2571, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h2563, h2570, h4, hc12, hc23, hlam, hphi]
                · linarith only [h2562, h2569, h4, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2678 | h2678
              · linarith only [h2563, h2678, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2680 | h2680
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2681 | h2681
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2682 | h2682
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2683 | h2683
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2684 | h2684
                        · linarith only [h2, h2566, h2684, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2686 | h2686
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2687 | h2687
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2688 | h2688
                              · linarith only [h2566, h2680, h2688, hc14, hlam, hphi, ht01, u0ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2690 | h2690
                                · linarith only [h2566, h2681, h2686, h2688, h2690, hc12, hlam, hphi, ht01, u0ehi3]
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
                                    linarith only [h4, hc12, hc23, hlam, hphi, p2692_1]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h4, hlam, p2692_0]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    rcases p2692_3 (m.d 0 2) (by simp) with h2696 | h2696
                                    · rcases p2692_3 (m.d 1 2) (by simp) with h2697 | h2697
                                      · linarith only [h0, h2697, hlam]
                                      · linarith only [h2680, h2697, hlam]
                                    · linarith only [h2696, hlam, p2692_0]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h2687, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2692_1, u5ehi3]
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
                                    linarith only [h2678, hlam, p2692_0]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    rcases p2692_3 (m.d 0 2) (by simp) with h2705 | h2705
                                    · rcases p2692_3 (m.d 1 2) (by simp) with h2706 | h2706
                                      · rcases p2692_3 (m.d 2 3) (by simp) with h2707 | h2707
                                        · rcases p2692_3 (m.d 2 4) (by simp) with h2708 | h2708
                                          · linarith only [h2708, hlam, p2692_0]
                                          · rcases p2692_3 (m.d 2 5) (by simp) with h2710 | h2710
                                            · linarith only [h2681, h2710, hlam]
                                            · linarith only [h2688, h2710, hlam]
                                        · linarith only [h2686, h2707, hlam]
                                      · linarith only [h2706, hlam, p2692_0]
                                    · linarith only [h2562, h2705, hlam]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h0, h2687, hc01, hlam, hphi, ht0b, ht5b, p2692_1, u5ehi3]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p2692_1, u0ehi1]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h2681, h2687, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2692_1, u5ehi3]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [hlam, p2692_0]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    rcases p2692_3 (m.d 0 2) (by simp) with h2720 | h2720
                                    · linarith only [h2720, h4, hlam]
                                    · linarith only [h2562, h2720, hlam]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    rcases p2692_3 (m.d 0 2) (by simp) with h2723 | h2723
                                    · linarith only [h2723, h4, hlam]
                                    · linarith only [h2563, h2723, hlam]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h2562, hlam, p2692_0]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h2680, hlam, p2692_0]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h2686, hlam, p2692_1]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [hlam, p2692_0]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h2688, hlam, p2692_1]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h2563, hlam, p2692_0]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h2681, hlam, p2692_0]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h2687, hlam, p2692_1]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [h0, h2681, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2692_1]
                                  · have p2692_0 := h2692c.1
                                    have p2692_1 := h2692c.2.1
                                    have p2692_2 := h2692c.2.2.1
                                    have p2692_3 := h2692c.2.2.2
                                    linarith only [hlam, p2692_0]
                            · linarith only [h0, h2681, h2687, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h0, h2681, h2686, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h2563, h2565, h2678, h2681, h2683, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · linarith only [h2564, h2678, h2681, h2682, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h2563, h2681, h4, hc12, hc23, hlam, hphi]
                · linarith only [h2562, h2680, h4, hc12, hc23, hlam, hphi]
          · linarith only [h2563, h2565, h4, hlam]
        · linarith only [h2562, h2564, h4, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2744 | h2744
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2745 | h2745
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2746 | h2746
            · linarith only [h2562, h2563, h2746, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2748 | h2748
              · linarith only [h0, h2748, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2750 | h2750
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2751 | h2751
                  · linarith only [h0, h2563, h2751, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2753 | h2753
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2754 | h2754
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2755 | h2755
                        · linarith only [h2, h2746, h2755, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2757 | h2757
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2758 | h2758
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2759 | h2759
                              · linarith only [h0, h2, h2563, h2746, h2750, h2758, h2759, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2761 | h2761
                                · linarith only [h0, h2563, h2750, h2757, h2759, h2761, hlam]
                                · rcases h2bigk with h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c | h2763c
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [hlam, p2763_0]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2563, h2759, hc12, hc45, hlam, hphi, ht23, ht34, p2763_1]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h4, hlam, p2763_0]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2563, h2757, h2759, hc34, hc45, hlam, hphi, p2763_1]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2563, hlam, p2763_0]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h0, hlam, p2763_0]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [hlam, p2763_0]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2748, hlam, p2763_0]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h0, h2563, h2757, h2759, hc34, hc45, hlam, hphi, p2763_1]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2751, hlam, p2763_0]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p2763_1, u0ehi1]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    rcases p2763_3 (m.d 0 2) (by simp) with h2775 | h2775
                                    · linarith only [h2775, h4, hlam]
                                    · linarith only [h0, h2775, hlam]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [hlam, p2763_0]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    rcases p2763_3 (m.d 0 2) (by simp) with h2779 | h2779
                                    · linarith only [h2779, h4, hlam]
                                    · linarith only [h2562, h2779, hlam]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2562, h2563, hc23, hlam, hphi, ht01, ht12, p2763_1, u0ehi3]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2562, hlam, p2763_0]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2750, hlam, p2763_0]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2757, hlam, p2763_1]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [hlam, p2763_0]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2759, hlam, p2763_1]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2562, hc25, hlam, hphi, ht01, ht12, p2763_1, u0ehi3]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2750, h2757, h2759, hc34, hc45, hlam, hphi, p2763_1]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [h2758, hlam, p2763_1]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    rcases p2763_3 (m.d 0 2) (by simp) with h2791 | h2791
                                    · linarith only [h2563, h2791, hlam]
                                    · linarith only [h2562, h2791, hlam]
                                  · have p2763_0 := h2763c.1
                                    have p2763_1 := h2763c.2.1
                                    have p2763_2 := h2763c.2.2.1
                                    have p2763_3 := h2763c.2.2.2
                                    linarith only [hlam, p2763_0]
                            · linarith only [h1, h2562, h2754, h2758, h4, hc03, hlam, hphi, u0ehi3]
                          · linarith only [h2562, h2757, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2797 | h2797
                        · linarith only [h2, h2746, h2797, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2799 | h2799
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2800 | h2800
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2801 | h2801
                              · linarith only [h2745, h2746, h2748, h2750, h2754, h2801, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2803 | h2803
                                · linarith only [h2563, h2745, h2748, h2750, h2754, h2799, h2801, h2803, h4, hc02, hc23, hlam, hphi]
                                · rcases h2bigk with h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [hlam, p2805_0]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2563, h2750, h2799, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2805_1]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h4, hlam, p2805_0]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2563, h2799, h2801, hc34, hc45, hlam, hphi, p2805_1]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2563, hlam, p2805_0]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h0, hlam, p2805_0]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [hlam, p2805_0]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2748, hlam, p2805_0]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h0, h2563, h2799, h2801, hc34, hc45, hlam, hphi, p2805_1]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2751, hlam, p2805_0]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p2805_1, u0ehi1]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    rcases p2805_3 (m.d 0 2) (by simp) with h2817 | h2817
                                    · linarith only [h2817, h4, hlam]
                                    · linarith only [h0, h2817, hlam]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [hlam, p2805_0]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2745, h2748, h2750, h2754, h4, hlam, p2805_2]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2562, h2563, hc23, hlam, hphi, ht01, ht12, p2805_1, u0ehi3]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2562, hlam, p2805_0]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2750, hlam, p2805_0]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2799, hlam, p2805_1]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [hlam, p2805_0]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2801, hlam, p2805_1]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2562, h2801, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p2805_1, u0ehi3]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2750, h2801, hc24, hc45, hlam, hphi, p2805_1]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [h2800, hlam, p2805_1]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    rcases p2805_3 (m.d 0 2) (by simp) with h2831 | h2831
                                    · linarith only [h2563, h2831, hlam]
                                    · linarith only [h2562, h2831, hlam]
                                  · have p2805_0 := h2805c.1
                                    have p2805_1 := h2805c.2.1
                                    have p2805_2 := h2805c.2.2.1
                                    have p2805_3 := h2805c.2.2.2
                                    linarith only [hlam, p2805_0]
                            · linarith only [h2745, h2800, h4, hlam]
                          · linarith only [h2745, h2748, h2750, h2754, h2799, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h2744, h2746, h2748, h2750, h2753, hc24, hc45, hlam, hphi]
                · linarith only [h2562, h2750, h4, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2839 | h2839
            · linarith only [h2562, h2745, h2839, h4, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2841 | h2841
              · linarith only [h2841, h4, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2843 | h2843
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2844 | h2844
                  · linarith only [h2562, h2563, h2844, hc12, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2846 | h2846
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2847 | h2847
                      · linarith only [h1, h2745, h2847, hc01, hlam, hphi, u0ehi2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2849 | h2849
                        · linarith only [h2, h2839, h2849, hc01, hlam, hphi, u0ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2851 | h2851
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2852 | h2852
                            · linarith only [h2562, h2745, h2852, h4, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                            · linarith only [h2562, h2852, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · linarith only [h2562, h2851, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · linarith only [h2744, h2745, h2846, hc13, hc35, hlam, hphi]
                · linarith only [h2562, h2843, h4, hc12, hc23, hlam, hphi]
        · linarith only [h2562, h2744, h4, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2859 | h2859
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2860 | h2860
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2861 | h2861
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2862 | h2862
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2863 | h2863
              · linarith only [h0, h2863, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2865 | h2865
                · linarith only [h2562, h2859, h2865, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2867 | h2867
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2868 | h2868
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2869 | h2869
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2870 | h2870
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2871 | h2871
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2872 | h2872
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2873 | h2873
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2874 | h2874
                                · linarith only [h1, h2868, h2874, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases h2bigk with h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2562, h2867, h2871, h2873, h2874, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2876_1]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h4, hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2562, hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2562, h2871, h2873, h2874, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2876_1]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h0, hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2863, hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2865, hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h0, h2873, h2874, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2876_1]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p2876_1, u0ehi1]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2867, h2873, h2874, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2876_1]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2562, h2859, h2873, h2874, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2876_1]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    rcases p2876_3 (m.d 0 2) (by simp) with h2891 | h2891
                                    · linarith only [h2891, h4, hlam]
                                    · linarith only [h2859, h2891, hlam]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h0, h2867, h2873, h2874, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2876_1]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2867, h2873, h2874, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2876_1]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2871, hlam, p2876_1]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    rcases p2876_3 (m.d 0 2) (by simp) with h2898 | h2898
                                    · linarith only [h2562, h2898, hlam]
                                    · linarith only [h2859, h2898, hlam]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2859, hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2867, hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2872, hlam, p2876_1]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [h2873, hlam, p2876_0]
                                  · have p2876_0 := h2876c.1
                                    have p2876_1 := h2876c.2.1
                                    have p2876_2 := h2876c.2.2.1
                                    have p2876_3 := h2876c.2.2.2
                                    linarith only [hlam, p2876_0]
                              · linarith only [h0, h2562, h2867, h2873, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                            · linarith only [h0, h2562, h2867, h2871, h2872, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h0, h2867, h2871, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h2862, h2865, h2867, h2870, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h2859, h2861, h2863, h2867, h2869, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · linarith only [h2860, h2863, h2867, h2868, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h2859, h2867, h4, hc12, hc23, hlam, hphi]
            · linarith only [h2562, h2859, h2862, hlam]
          · linarith only [h2859, h2861, h4, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2915 | h2915
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2916 | h2916
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2917 | h2917
              · linarith only [h2859, h2917, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2919 | h2919
                · linarith only [h2562, h2859, h2919, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2921 | h2921
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2922 | h2922
                    · linarith only [h1, h2860, h2922, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2924 | h2924
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2925 | h2925
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2926 | h2926
                          · linarith only [h0, h2860, h2921, h2926, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · linarith only [h0, h2921, h2926, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h2916, h2922, h2924, h2925, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · linarith only [h2915, h2917, h2921, h2924, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · linarith only [h2859, h2860, h2921, h4, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h2859, h2860, h2916, h4, hlam]
          · linarith only [h2859, h2915, h4, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2934 | h2934
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2935 | h2935
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2936 | h2936
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2937 | h2937
              · linarith only [h0, h2937, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2939 | h2939
                · linarith only [h0, h2562, h2939, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2941 | h2941
                  · linarith only [h0, h2859, h2941, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2943 | h2943
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2944 | h2944
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2945 | h2945
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2946 | h2946
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2947 | h2947
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2948 | h2948
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2949 | h2949
                                · linarith only [h1, h2943, h2949, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases h2bigk with h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2859, h2946, h2948, hc12, hc23, hlam, hphi, p2951_1]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h4, hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2562, hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2859, hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h0, hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2937, hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2939, hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2941, hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p2951_1, u0ehi1]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    rcases p2951_3 (m.d 0 2) (by simp) with h2963 | h2963
                                    · linarith only [h2963, h4, hlam]
                                    · linarith only [h0, h2963, hlam]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2562, hc23, hlam, hphi, ht01, ht12, p2951_1, u0ehi1]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2859, hc23, hlam, hphi, ht01, ht12, p2951_1, u0ehi1]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [hc24, hlam, hphi, ht01, ht12, p2951_1, u0ehi1]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    rcases p2951_3 (m.d 0 2) (by simp) with h2970 | h2970
                                    · linarith only [h2562, h2970, hlam]
                                    · linarith only [h0, h2970, hlam]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2946, hlam, p2951_1]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2859, h2946, hc23, hlam, hphi, ht01, ht12, p2951_1, u0ehi1]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [hc25, hlam, hphi, ht01, ht12, p2951_1, u0ehi1]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    rcases p2951_3 (m.d 0 2) (by simp) with h2977 | h2977
                                    · linarith only [h2859, h2977, hlam]
                                    · linarith only [h0, h2977, hlam]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2947, hlam, p2951_1]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [h2948, hlam, p2951_0]
                                  · have p2951_0 := h2951c.1
                                    have p2951_1 := h2951c.2.1
                                    have p2951_2 := h2951c.2.2.1
                                    have p2951_3 := h2951c.2.2.2
                                    linarith only [hlam, p2951_0]
                              · linarith only [h2, h2562, h2945, h2948, hc04, hlam, hphi, u0ehi1]
                            · linarith only [h2947, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h2946, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2986 | h2986
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2987 | h2987
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2988 | h2988
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2989 | h2989
                                · linarith only [h2943, h2945, h2989, hlam]
                                · rcases h2bigk with h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c | h2991c
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h4, hc12, hc23, hlam, hphi, p2991_1]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h4, hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h2562, hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h2859, hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h0, hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h2937, hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h2939, hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h2941, hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p2991_1, u0ehi1]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    rcases p2991_3 (m.d 0 2) (by simp) with h3003 | h3003
                                    · linarith only [h3003, h4, hlam]
                                    · linarith only [h0, h3003, hlam]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h2562, hc23, hlam, hphi, ht01, ht12, p2991_1, u0ehi3]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h2859, hc23, hlam, hphi, ht01, ht12, p2991_1, u0ehi1]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [hc24, hlam, hphi, ht01, ht12, p2991_1, u0ehi1]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    rcases p2991_3 (m.d 0 2) (by simp) with h3010 | h3010
                                    · linarith only [h2562, h3010, hlam]
                                    · linarith only [h0, h3010, hlam]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h2986, hlam, p2991_1]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h2859, h2986, hc23, hlam, hphi, ht01, ht12, p2991_1, u0ehi1]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [hc25, hlam, hphi, ht01, ht12, p2991_1, u0ehi1]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    rcases p2991_3 (m.d 0 2) (by simp) with h3017 | h3017
                                    · linarith only [h2859, h3017, hlam]
                                    · linarith only [h0, h3017, hlam]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h2987, hlam, p2991_1]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [h2988, hlam, p2991_0]
                                  · have p2991_0 := h2991c.1
                                    have p2991_1 := h2991c.2.1
                                    have p2991_2 := h2991c.2.2.1
                                    have p2991_3 := h2991c.2.2.2
                                    linarith only [hlam, p2991_0]
                              · linarith only [h2562, h2936, h2988, hc04, hlam, hphi, u0ehi1]
                            · linarith only [h2934, h2936, h2944, h2945, h2987, h4, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h2986, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3026 | h3026
                        · linarith only [h2935, h2943, h2944, h3026, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3028 | h3028
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3029 | h3029
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3030 | h3030
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3031 | h3031
                                · linarith only [h2935, h2943, h2944, h3026, h3031, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases h2bigk with h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c | h3033c
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h2859, h3028, h3030, hc12, hc23, hlam, hphi, p3033_1]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h4, hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h2562, hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h2859, hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h0, hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h2937, hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h2939, hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h2941, hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p3033_1, u0ehi1]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    rcases p3033_3 (m.d 0 2) (by simp) with h3045 | h3045
                                    · linarith only [h3045, h4, hlam]
                                    · linarith only [h0, h3045, hlam]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h2562, hc23, hlam, hphi, ht01, ht12, p3033_1, u0ehi1]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h2859, hc23, hlam, hphi, ht01, ht12, p3033_1, u0ehi1]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [hc24, hlam, hphi, ht01, ht12, p3033_1, u0ehi1]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    rcases p3033_3 (m.d 0 2) (by simp) with h3052 | h3052
                                    · linarith only [h2562, h3052, hlam]
                                    · linarith only [h0, h3052, hlam]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h3028, hlam, p3033_1]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h2859, h3028, hc23, hlam, hphi, ht01, ht12, p3033_1, u0ehi4]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [hc25, hlam, hphi, ht01, ht12, p3033_1, u0ehi1]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    rcases p3033_3 (m.d 0 2) (by simp) with h3059 | h3059
                                    · linarith only [h2859, h3059, hlam]
                                    · linarith only [h0, h3059, hlam]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h3029, hlam, p3033_1]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [h3030, hlam, p3033_0]
                                  · have p3033_0 := h3033c.1
                                    have p3033_1 := h3033c.2.1
                                    have p3033_2 := h3033c.2.2.1
                                    have p3033_3 := h3033c.2.2.2
                                    linarith only [hlam, p3033_0]
                              · linarith only [h2562, h2934, h2936, h3030, h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h3029, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h2935, h2943, h2944, h3028, h4, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3068 | h3068
                      · linarith only [h2934, h2943, h3068, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3070 | h3070
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3071 | h3071
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3072 | h3072
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3073 | h3073
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3074 | h3074
                                · rcases h2bigk with h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c | h3075c
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h2859, h3073, hc12, hc24, hlam, hphi, p3075_1]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h4, hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h2562, hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h2859, hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h0, hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h2937, hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h2939, hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h2941, hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht01, ht12, p3075_1, u0ehi1]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    rcases p3075_3 (m.d 0 2) (by simp) with h3087 | h3087
                                    · linarith only [h3087, h4, hlam]
                                    · linarith only [h0, h3087, hlam]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h2562, hc23, hlam, hphi, ht01, ht12, p3075_1, u0ehi1]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h2859, hc23, hlam, hphi, ht01, ht12, p3075_1, u0ehi1]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [hc24, hlam, hphi, ht01, ht12, p3075_1, u0ehi1]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    rcases p3075_3 (m.d 0 2) (by simp) with h3094 | h3094
                                    · linarith only [h2562, h3094, hlam]
                                    · linarith only [h0, h3094, hlam]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h3071, hlam, p3075_1]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h2859, h3071, hc23, hlam, hphi, ht01, ht12, p3075_1, u0ehi1]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [hc25, hlam, hphi, ht01, ht12, p3075_1, u0ehi1]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    rcases p3075_3 (m.d 0 2) (by simp) with h3101 | h3101
                                    · linarith only [h2859, h3101, hlam]
                                    · linarith only [h0, h3101, hlam]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h3072, hlam, p3075_1]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [h3073, hlam, p3075_0]
                                  · have p3075_0 := h3075c.1
                                    have p3075_1 := h3075c.2.1
                                    have p3075_2 := h3075c.2.2.1
                                    have p3075_3 := h3075c.2.2.2
                                    linarith only [hlam, p3075_0]
                                · linarith only [h2, h2937, h2943, h3070, h3074, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h2562, h2934, h2943, h3070, h3073, h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h2934, h2943, h3070, h3072, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · linarith only [h2934, h3071, h4, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3111 | h3111
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3112 | h3112
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3113 | h3113
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3114 | h3114
                                · linarith only [h2934, h2939, h3070, h3114, h4, hc12, hc23, hlam, hphi]
                                · linarith only [h2934, h2936, h2937, h2943, h3114, h4, hc12, hc23, hlam, hphi]
                              · linarith only [h2562, h2934, h2936, h3113, h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h2935, h3112, h4, hlam]
                          · linarith only [h3111, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3120 | h3120
              · linarith only [h3120, h4, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3122 | h3122
                · linarith only [h2562, h3122, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3124 | h3124
                  · linarith only [h0, h2859, h3124, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3126 | h3126
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3127 | h3127
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3128 | h3128
                        · linarith only [h2936, h3128, hc14, hlam, hphi, ht01, u0ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3130 | h3130
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3131 | h3131
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3132 | h3132
                              · linarith only [h2562, h2936, h3130, h3132, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h2562, h3132, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                            · linarith only [h1, h3127, h3131, h4, hc01, hlam, hphi, u0ehi1]
                          · linarith only [h1, h3126, h3130, h4, hc01, hlam, hphi, u0ehi2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3137 | h3137
                        · linarith only [h2935, h3126, h3127, h3137, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3139 | h3139
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3140 | h3140
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3141 | h3141
                              · linarith only [h2562, h2936, h3141, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h2562, h3141, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                            · linarith only [h2935, h3140, h4, hc03, hlam, hphi, u0ehi1]
                          · linarith only [h2935, h3126, h3127, h3139, h4, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3146 | h3146
                      · linarith only [h2934, h2936, h3126, h3146, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3148 | h3148
                        · linarith only [h2936, h3148, hc14, hlam, hphi, ht01, u0ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3150 | h3150
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3151 | h3151
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3152 | h3152
                              · linarith only [h2562, h2936, h3152, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h2562, h3152, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                            · linarith only [h3151, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h2934, h3150, h4, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3157 | h3157
            · linarith only [h2934, h2935, h3157, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3159 | h3159
              · linarith only [h3159, h4, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3161 | h3161
                · linarith only [h0, h2562, h3161, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3163 | h3163
                  · linarith only [h0, h2859, h3163, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3165 | h3165
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3166 | h3166
                      · linarith only [h2562, h2934, h2935, h3166, hc13, hlam, hphi, ht01, u0ehi1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3168 | h3168
                        · linarith only [h2562, h3157, h3168, hc14, hlam, hphi, ht01, u0ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3170 | h3170
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3171 | h3171
                            · linarith only [h2562, h2934, h2935, h3171, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h3171, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h1, h3165, h3170, h4, hc03, hlam, hphi, u0ehi1]
                    · linarith only [h2934, h2935, h3165, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3176 | h3176
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3177 | h3177
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3178 | h3178
              · linarith only [h0, h3178, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3180 | h3180
                · linarith only [h0, h2562, h3180, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3182 | h3182
                  · linarith only [h0, h2859, h3182, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3184 | h3184
                    · linarith only [h2934, h3176, h3184, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3186 | h3186
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3187 | h3187
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3188 | h3188
                          · linarith only [h2859, h2934, h3176, h3188, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                          · linarith only [h3188, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h3177, h3184, h3186, h3187, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · linarith only [h2934, h3176, h3186, hc13, hc34, hlam, hphi]
            · linarith only [h2934, h3176, h3177, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3194 | h3194
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3195 | h3195
              · linarith only [h3195, h4, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3197 | h3197
                · linarith only [h0, h2562, h3197, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3199 | h3199
                  · linarith only [h0, h2859, h3199, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3201 | h3201
                    · linarith only [h1, h2934, h3201, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3203 | h3203
                      · linarith only [h3176, h3201, h3203, hc14, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3205 | h3205
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3206 | h3206
                          · linarith only [h2934, h3206, h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                          · linarith only [h3206, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3209 | h3209
                          · linarith only [h2934, h3209, h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                          · linarith only [h3209, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3212 | h3212
              · linarith only [h3212, h4, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3214 | h3214
                · linarith only [h2562, h3214, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3216 | h3216
                  · linarith only [h0, h2859, h3216, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3218 | h3218
                    · linarith only [h1, h2934, h3218, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3220 | h3220
                      · linarith only [h1, h3176, h3220, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3222 | h3222
                        · linarith only [h3194, h3222, hc14, hlam, hphi, ht01, u0ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3224 | h3224
                          · linarith only [h2934, h3224, h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                          · linarith only [h3224, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

set_option maxHeartbeats 6678000 in
set_option maxHeartbeats 6678000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s2 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s3 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3227 | h3227
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3228 | h3228
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3229 | h3229
        · linarith only [h0, h3, h3229, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3231 | h3231
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3232 | h3232
            · linarith only [h1, h3, h3232, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3234 | h3234
              · linarith only [h2, h3, h3234, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3236 | h3236
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3237 | h3237
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3238 | h3238
                    · linarith only [h0, h3, h3229, h3238, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3240 | h3240
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3241 | h3241
                        · linarith only [h0, h3, h3231, h3232, h3236, h3238, h3241, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                        · linarith only [h0, h3, h3236, h3241, hc23, hc35, hlam, hphi]
                      · linarith only [h3231, h3232, h3240, hc13, hc35, hlam, hphi]
                  · linarith only [h3228, h3229, h3237, hc12, hc25, hlam, hphi]
                · linarith only [h3227, h3229, h3236, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3247 | h3247
            · linarith only [h1, h3, h3247, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3249 | h3249
              · linarith only [h0, h3, h3228, h3249, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3251 | h3251
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3252 | h3252
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3253 | h3253
                    · linarith only [h0, h3, h3253, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3255 | h3255
                      · linarith only [h3231, h3255, hc13, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3257 | h3257
                        · linarith only [h0, h3, h3247, h3252, h3253, h3255, h3257, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · linarith only [h0, h3, h3251, h3257, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h3, h3228, h3251, h3252, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h3227, h3229, h3251, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3262 | h3262
        · linarith only [h2, h3, h3228, h3262, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3264 | h3264
          · linarith only [h3227, h3228, h3264, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3266 | h3266
            · linarith only [h0, h3, h3227, h3266, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3268 | h3268
              · linarith only [h2, h3, h3268, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3270 | h3270
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3271 | h3271
                  · linarith only [h0, h3, h3228, h3271, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3273 | h3273
                    · linarith only [h2, h3, h3227, h3262, h3271, h3273, hc15, hlam, hphi, ht01, u0ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3275 | h3275
                      · linarith only [h3264, h3275, hc13, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3277 | h3277
                        · linarith only [h2, h3, h3266, h3270, h3271, h3273, h3277, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                        · linarith only [h2, h3, h3270, h3271, h3277, hc23, hc35, hlam, hphi]
                · linarith only [h3227, h3228, h3268, h3270, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3281 | h3281
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3282 | h3282
        · linarith only [h0, h3, h3282, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3284 | h3284
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3285 | h3285
            · linarith only [h1, h3, h3285, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3287 | h3287
              · linarith only [h0, h3, h3281, h3287, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3289 | h3289
                · linarith only [h3227, h3289, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3291 | h3291
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3292 | h3292
                    · linarith only [h1, h3281, h3282, h3289, h3292, hc01, hlam, hphi, u0ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3294 | h3294
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3295 | h3295
                        · linarith only [h1, h3, h3292, h3295, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3297 | h3297
                          · linarith only [h1, h3, h3287, h3289, h3291, h3295, h3297, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                          · linarith only [h1, h3, h3289, h3291, h3297, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h3, h3284, h3289, h3291, h3294, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h3227, h3281, h3291, hc12, hc23, hlam, hphi]
          · linarith only [h3227, h3281, h3284, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3303 | h3303
        · linarith only [h0, h3, h3303, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3305 | h3305
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3306 | h3306
            · linarith only [h1, h3, h3306, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3308 | h3308
              · linarith only [h1, h3, h3305, h3308, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3310 | h3310
                · linarith only [h3227, h3310, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3312 | h3312
                  · linarith only [h3281, h3312, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3314 | h3314
                    · linarith only [h1, h3303, h3310, h3314, hc01, hlam, hphi, u0ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3316 | h3316
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3317 | h3317
                        · linarith only [h1, h3, h3314, h3317, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3319 | h3319
                          · linarith only [h1, h3, h3308, h3316, h3317, h3319, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                          · linarith only [h1, h3, h3316, h3319, hc34, hc45, hlam, hphi]
                      · linarith only [h3305, h3306, h3316, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3323 | h3323
            · linarith only [h1, h3, h3323, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3325 | h3325
              · linarith only [h2, h3, h3325, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3327 | h3327
                · linarith only [h3227, h3327, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3329 | h3329
                  · linarith only [h3281, h3329, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3331 | h3331
                    · linarith only [h1, h3, h3327, h3331, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3333 | h3333
                      · linarith only [h1, h3, h3305, h3331, h3333, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3335 | h3335
                        · linarith only [h2, h3, h3227, h3323, h3331, h3333, h3335, hc25, hlam, hphi, ht01, ht12, u0ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3337 | h3337
                          · linarith only [h2, h3, h3227, h3305, h3325, h3335, h3337, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3339 | h3339
                            · linarith only [h3227, h3305, h3339, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h3227, h3339, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

set_option maxHeartbeats 6978000 in
set_option maxHeartbeats 6978000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s2 m hb0 hb2 hb3 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3342 | h3342
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3343 | h3343
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3344 | h3344
        · linarith only [h0, h2, h3344, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3346 | h3346
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3347 | h3347
            · linarith only [h1, h2, h3347, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3349 | h3349
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3350 | h3350
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3351 | h3351
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3352 | h3352
                    · linarith only [h0, h3343, h3344, h3349, h3352, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3354 | h3354
                      · linarith only [h0, h2, h3352, h3354, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h2, h3346, h3351, h3352, h3354, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h3343, h3344, h3351, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h3349, h3350, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3359 | h3359
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3360 | h3360
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3361 | h3361
                    · linarith only [h0, h3344, h3346, h3361, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3363 | h3363
                      · linarith only [h0, h2, h3361, h3363, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h2, h3346, h3360, h3361, h3363, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h3343, h3344, h3360, hc12, hc24, hlam, hphi]
                · linarith only [h2, h3342, h3359, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3368 | h3368
            · linarith only [h1, h2, h3368, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3370 | h3370
              · linarith only [h3343, h3346, h3370, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3372 | h3372
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3373 | h3373
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3374 | h3374
                    · linarith only [h0, h2, h3343, h3344, h3374, hc14, hlam, hphi, ht01, u0ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3376 | h3376
                      · linarith only [h0, h2, h3343, h3346, h3374, h3376, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3378 | h3378
                        · linarith only [h2, h3342, h3368, h3373, h3374, h3376, h3378, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                        · linarith only [h2, h3342, h3373, h3376, h3378, hc23, hc34, hlam, hphi]
                  · linarith only [h3343, h3346, h3373, hc12, hc25, hlam, hphi]
                · linarith only [h2, h3342, h3372, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3383 | h3383
        · linarith only [h0, h2, h3383, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3385 | h3385
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3386 | h3386
            · linarith only [h1, h2, h3386, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3388 | h3388
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3389 | h3389
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3390 | h3390
                  · linarith only [h3343, h3385, h3390, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3392 | h3392
                    · linarith only [h1, h3383, h3385, h3390, h3392, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3394 | h3394
                      · linarith only [h1, h2, h3390, h3392, h3394, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h3343, h3385, h3394, hc12, hc23, hlam, hphi]
                · linarith only [h1, h2, h3343, h3385, h3389, hlam]
              · linarith only [h3343, h3385, h3388, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3399 | h3399
            · linarith only [h1, h2, h3399, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3401 | h3401
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3402 | h3402
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3403 | h3403
                  · linarith only [h3343, h3403, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3405 | h3405
                    · linarith only [h1, h3383, h3403, h3405, hc01, hlam, hphi, u0ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3407 | h3407
                      · linarith only [h1, h2, h3385, h3403, h3405, h3407, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3409 | h3409
                        · linarith only [h1, h2, h3399, h3405, h3409, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3411 | h3411
                          · linarith only [h1, h2, h3409, h3411, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h1, h2, h3401, h3403, h3409, h3411, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h2, h3342, h3402, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3415 | h3415
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3416 | h3416
                  · linarith only [h3343, h3416, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3418 | h3418
                    · linarith only [h1, h3383, h3416, h3418, hc01, hlam, hphi, u0ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3420 | h3420
                      · linarith only [h1, h2, h3385, h3416, h3418, h3420, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3422 | h3422
                        · linarith only [h1, h2, h3399, h3418, h3422, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3424 | h3424
                          · linarith only [h1, h2, h3401, h3422, h3424, hc03, hc34, hlam, hphi]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3426 | h3426
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3427 | h3427
                              · linarith only [h2, h3342, h3416, h3422, h3424, h3427, hc12, hc23, hlam, hphi]
                              · linarith only [h3343, h3427, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h2, h3342, h3343, h3401, h3426, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                · linarith only [h2, h3342, h3415, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3432 | h3432
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3433 | h3433
        · linarith only [h0, h2, h3433, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3435 | h3435
          · linarith only [h0, h3342, h3435, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3437 | h3437
            · linarith only [h1, h2, h3437, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3439 | h3439
              · linarith only [h0, h3342, h3432, h3439, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3441 | h3441
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3442 | h3442
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3443 | h3443
                    · linarith only [h0, h2, h3433, h3443, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3445 | h3445
                      · linarith only [h0, h2, h3432, h3435, h3443, h3445, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3447 | h3447
                        · linarith only [h3437, h3447, hc13, hlam, hphi, ht01, u0ehi2]
                        · linarith only [h0, h2, h3442, h3447, hc23, hc34, hlam, hphi]
                  · linarith only [h3432, h3433, h3442, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3451 | h3451
                  · linarith only [h0, h2, h3441, h3451, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h3432, h3441, h3451, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3454 | h3454
        · linarith only [h1, h2, h3432, h3454, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3456 | h3456
          · linarith only [h1, h3342, h3432, h3456, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3458 | h3458
            · linarith only [h1, h2, h3458, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3460 | h3460
              · linarith only [h1, h3342, h3460, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3462 | h3462
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3463 | h3463
                  · linarith only [h3432, h3463, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3465 | h3465
                    · linarith only [h1, h3454, h3463, h3465, hc01, hlam, hphi, u0ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3467 | h3467
                      · linarith only [h1, h2, h3456, h3463, h3465, h3467, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3469 | h3469
                        · linarith only [h1, h2, h3458, h3462, h3465, h3469, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3471 | h3471
                          · linarith only [h1, h2, h3460, h3469, h3471, hc03, hc34, hlam, hphi]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3473 | h3473
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3474 | h3474
                              · linarith only [h1, h3342, h3463, h3469, h3473, h3474, hc12, hc23, hlam, hphi]
                              · linarith only [h3432, h3474, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h1, h2, h3462, h3463, h3473, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3478 | h3478
                  · linarith only [h3432, h3478, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3480 | h3480
                    · linarith only [h1, h2, h3462, h3478, h3480, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3482 | h3482
                      · linarith only [h1, h2, h3456, h3462, h3478, h3482, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3484 | h3484
                        · linarith only [h1, h2, h3462, h3484, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3486 | h3486
                          · linarith only [h1, h2, h3462, h3486, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3488 | h3488
                            · linarith only [h1, h2, h3462, h3478, h3480, h3488, hc12, hc24, hlam, hphi]
                            · linarith only [h1, h2, h3432, h3488, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]

end R2N4
