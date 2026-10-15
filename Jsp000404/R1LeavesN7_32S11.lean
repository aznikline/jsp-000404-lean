import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2629 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h2630 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h2631 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h2632 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2633 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h2634 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 2 3 4 (by decide) (by decide) with h2635 | h2635
  · rcases m.htr 2 3 5 (by decide) (by decide) with h2636 | h2636
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2637 | h2637
      · linarith only [h2010, h2014, h2637, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h2639 | h2639
        · linarith only [h2010, h2014, h2635, h2639, hlam]
        · rcases h2bigk with h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c | h2641c
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h0, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            rcases p2641_3 (m.d 0 2) (by simp) with h2644 | h2644
            · rcases p2641_3 (m.d 1 2) (by simp) with h2645 | h2645
              · rcases p2641_3 (m.d 2 3) (by simp) with h2646 | h2646
                · linarith only [h2646, hlam, p2641_0]
                · rcases p2641_3 (m.d 2 4) (by simp) with h2648 | h2648
                  · linarith only [h2010, h2648, hlam]
                  · rcases p2641_3 (m.d 2 5) (by simp) with h2650 | h2650
                    · linarith only [h2011, h2650, hlam]
                    · rcases h3bigk with h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h879, hlam, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2655 | h2655
                        · rcases p2652_3 (m.d 1 3) (by simp) with h2656 | h2656
                          · rcases p2652_3 (m.d 2 3) (by simp) with h2657 | h2657
                            · linarith only [h2009, h2657, hlam]
                            · rcases p2652_3 (m.d 3 4) (by simp) with h2659 | h2659
                              · linarith only [h2012, h2659, hlam]
                              · rcases p2652_3 (m.d 3 5) (by simp) with h2661 | h2661
                                · linarith only [h2013, h2661, hlam]
                                · rcases h3emax with h2663 | h2663 | h2663 | h2663 | h2663
                                  · linarith only [h2636, h2637, h2663, hlam, ht23, p2652_1, u2ehi3]
                                  · linarith only [h0, h2009, h2014, h2632, h2634, h2636, h2637, h2663, hc04, hc12, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, p2652_1, u2ehi3]
                                  · linarith only [h2636, h2637, h2663, hlam, ht23, u2ehi3]
                                  · rcases h5bigk with h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [hlam, p2667_0]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h1407, hlam, p2667_1]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2014, hc45, hlam, hphi, ht23, ht34, p2667_1, u2ehi4]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      rcases p2667_3 (m.d 0 5) (by simp) with h2671 | h2671
                                      · rcases p2667_3 (m.d 1 5) (by simp) with h2672 | h2672
                                        · rcases p2667_3 (m.d 2 5) (by simp) with h2673 | h2673
                                          · linarith only [h2011, h2673, hlam]
                                          · linarith only [h2636, h2673, hlam]
                                        · linarith only [h2633, h2672, hlam]
                                      · linarith only [h2013, h2671, hlam]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2014, hlam, p2667_0]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      rcases p2667_3 (m.d 0 5) (by simp) with h2679 | h2679
                                      · linarith only [h1407, h2679, hlam]
                                      · rcases p2667_3 (m.d 1 5) (by simp) with h2681 | h2681
                                        · rcases p2667_3 (m.d 2 5) (by simp) with h2682 | h2682
                                          · linarith only [h2631, h2682, hlam]
                                          · rcases p2667_3 (m.d 3 5) (by simp) with h2684 | h2684
                                            · linarith only [h2633, h2684, hlam]
                                            · rcases p2667_3 (m.d 4 5) (by simp) with h2686 | h2686
                                              · linarith only [h2634, h2686, hlam]
                                              · linarith only [h2014, h2686, hlam]
                                        · linarith only [h1407, h2681, hlam]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [hlam, p2667_0]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      rcases p2667_3 (m.d 0 5) (by simp) with h2691 | h2691
                                      · linarith only [h1407, h2691, hlam]
                                      · linarith only [h2011, h2691, hlam]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      rcases p2667_3 (m.d 0 5) (by simp) with h2694 | h2694
                                      · linarith only [h1407, h2694, hlam]
                                      · linarith only [h2013, h2694, hlam]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2010, h2014, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2667_1, u2ehi3]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2011, hlam, p2667_1]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2631, hlam, p2667_1]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [hlam, p2667_0]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2009, h2636, hc02, hc35, hlam, hphi, ht0b, ht5b, p2652_1, p2667_1]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2637, hlam, p2667_0]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2013, hlam, p2667_1]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2633, hlam, p2667_1]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2636, hlam, p2667_0]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [hlam, p2667_0]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2639, hlam, p2667_0]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2011, h2637, hc45, hlam, hphi, ht23, ht34, p2667_1, u2ehi3]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2634, hlam, p2667_1]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [h2629, h2632, h2634, h2637, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2667_1, u2ehi3]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      rcases p2667_3 (m.d 0 5) (by simp) with h2711 | h2711
                                      · linarith only [h2014, h2711, hlam]
                                      · linarith only [h2013, h2711, hlam]
                                    · have p2667_0 := h2667c.1
                                      have p2667_1 := h2667c.2.1
                                      have p2667_2 := h2667c.2.2.1
                                      have p2667_3 := h2667c.2.2.2
                                      linarith only [hlam, p2667_0]
                                  · rcases h5bigk with h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c | h2715c
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [hlam, p2715_0]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h1407, hlam, p2715_1]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2014, h2629, h2632, h2634, h2637, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2715_1, u2ehi3]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      rcases p2715_3 (m.d 0 5) (by simp) with h2719 | h2719
                                      · rcases p2715_3 (m.d 1 5) (by simp) with h2720 | h2720
                                        · rcases p2715_3 (m.d 2 5) (by simp) with h2721 | h2721
                                          · linarith only [h2011, h2721, hlam]
                                          · linarith only [h2636, h2721, hlam]
                                        · linarith only [h2633, h2720, hlam]
                                      · linarith only [h2013, h2719, hlam]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2014, hlam, p2715_0]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      rcases p2715_3 (m.d 0 5) (by simp) with h2727 | h2727
                                      · linarith only [h1407, h2727, hlam]
                                      · rcases p2715_3 (m.d 1 5) (by simp) with h2729 | h2729
                                        · rcases p2715_3 (m.d 2 5) (by simp) with h2730 | h2730
                                          · linarith only [h2631, h2730, hlam]
                                          · rcases p2715_3 (m.d 3 5) (by simp) with h2732 | h2732
                                            · linarith only [h2633, h2732, hlam]
                                            · rcases p2715_3 (m.d 4 5) (by simp) with h2734 | h2734
                                              · linarith only [h2634, h2734, hlam]
                                              · linarith only [h2014, h2734, hlam]
                                        · linarith only [h1407, h2729, hlam]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [hlam, p2715_0]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      rcases p2715_3 (m.d 0 5) (by simp) with h2739 | h2739
                                      · linarith only [h1407, h2739, hlam]
                                      · linarith only [h2011, h2739, hlam]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      rcases p2715_3 (m.d 0 5) (by simp) with h2742 | h2742
                                      · linarith only [h1407, h2742, hlam]
                                      · linarith only [h2013, h2742, hlam]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2010, h2014, h2629, h2632, h2634, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2715_1, u2ehi3]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2011, hlam, p2715_1]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2631, hlam, p2715_1]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [hlam, p2715_0]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2009, h2636, hc02, hc35, hlam, hphi, ht0b, ht5b, p2652_1, p2715_1]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2637, hlam, p2715_0]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2013, hlam, p2715_1]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2633, hlam, p2715_1]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2636, hlam, p2715_0]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [hlam, p2715_0]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2639, hlam, p2715_0]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h1407, h2629, h2632, h2634, hc01, hc12, hlam, hphi, p2715_1]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2634, hlam, p2715_1]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [h2629, h2632, h2634, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2715_1, u2ehi4]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      rcases p2715_3 (m.d 0 5) (by simp) with h2759 | h2759
                                      · linarith only [h2014, h2759, hlam]
                                      · linarith only [h2013, h2759, hlam]
                                    · have p2715_0 := h2715c.1
                                      have p2715_1 := h2715c.2.1
                                      have p2715_2 := h2715c.2.2.1
                                      have p2715_3 := h2715c.2.2.2
                                      linarith only [hlam, p2715_0]
                          · linarith only [h2629, h2656, hlam]
                        · linarith only [h2009, h2655, hlam]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2765 | h2765
                        · rcases p2652_3 (m.d 1 3) (by simp) with h2766 | h2766
                          · rcases p2652_3 (m.d 2 3) (by simp) with h2767 | h2767
                            · linarith only [h2009, h2767, hlam]
                            · linarith only [h2635, h2767, hlam]
                          · linarith only [h2632, h2766, hlam]
                        · linarith only [h2765, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2772 | h2772
                        · rcases p2652_3 (m.d 1 3) (by simp) with h2773 | h2773
                          · rcases p2652_3 (m.d 2 3) (by simp) with h2774 | h2774
                            · linarith only [h2009, h2774, hlam]
                            · linarith only [h2636, h2774, hlam]
                          · linarith only [h2633, h2773, hlam]
                        · linarith only [h2772, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2779 | h2779
                        · linarith only [h2779, h879, hlam]
                        · rcases p2652_3 (m.d 1 3) (by simp) with h2781 | h2781
                          · rcases p2652_3 (m.d 2 3) (by simp) with h2782 | h2782
                            · linarith only [h2629, h2782, hlam]
                            · rcases p2652_3 (m.d 3 4) (by simp) with h2784 | h2784
                              · linarith only [h2632, h2784, hlam]
                              · rcases p2652_3 (m.d 3 5) (by simp) with h2786 | h2786
                                · linarith only [h2633, h2786, hlam]
                                · rcases h3emax with h2788 | h2788 | h2788 | h2788 | h2788
                                  · linarith only [h2009, h2788, hlam, ht23, u2ehi2]
                                  · linarith only [h2788, h879, hc01, hlam, ht12, ht23]
                                  · linarith only [h2788, hlam, ht23, u2ehi2]
                                  · rcases h5bigk with h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c | h2792c
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h1407, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2013, h2629, h2637, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2652_1, p2792_1, u2ehi3]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2013, h2629, h2639, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2652_1, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2014, hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      rcases p2792_3 (m.d 0 5) (by simp) with h2798 | h2798
                                      · linarith only [h1407, h2798, hlam]
                                      · rcases p2792_3 (m.d 1 5) (by simp) with h2800 | h2800
                                        · rcases p2792_3 (m.d 2 5) (by simp) with h2801 | h2801
                                          · linarith only [h2631, h2801, hlam]
                                          · rcases p2792_3 (m.d 3 5) (by simp) with h2803 | h2803
                                            · linarith only [h2633, h2803, hlam]
                                            · rcases p2792_3 (m.d 4 5) (by simp) with h2805 | h2805
                                              · linarith only [h2634, h2805, hlam]
                                              · linarith only [h2014, h2805, hlam]
                                        · linarith only [h1407, h2800, hlam]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      rcases p2792_3 (m.d 0 5) (by simp) with h2810 | h2810
                                      · linarith only [h1407, h2810, hlam]
                                      · linarith only [h2011, h2810, hlam]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      rcases p2792_3 (m.d 0 5) (by simp) with h2813 | h2813
                                      · linarith only [h1407, h2813, hlam]
                                      · linarith only [h2013, h2813, hlam]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2010, h2014, h2629, h2632, h2634, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2792_1, u2ehi3]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2011, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2631, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2011, h2013, h2629, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2652_1, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2637, hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2013, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2633, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2636, hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2639, hlam, p2792_0]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2011, hc45, hlam, hphi, ht23, ht34, p2792_1, u2ehi4]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2634, hlam, p2792_1]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [h2629, h2632, h2634, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2792_1, u2ehi4]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      rcases p2792_3 (m.d 0 5) (by simp) with h2830 | h2830
                                      · linarith only [h2014, h2830, hlam]
                                      · linarith only [h2013, h2830, hlam]
                                    · have p2792_0 := h2792c.1
                                      have p2792_1 := h2792c.2.1
                                      have p2792_2 := h2792c.2.2.1
                                      have p2792_3 := h2792c.2.2.2
                                      linarith only [hlam, p2792_0]
                                  · rcases h5bigk with h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [hlam, p2834_0]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h1407, hlam, p2834_1]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2013, h2629, h2637, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2652_1, p2834_1, u2ehi3]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2013, h2629, h2639, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2652_1, p2834_1]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2014, hlam, p2834_0]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      rcases p2834_3 (m.d 0 5) (by simp) with h2840 | h2840
                                      · linarith only [h1407, h2840, hlam]
                                      · rcases p2834_3 (m.d 1 5) (by simp) with h2842 | h2842
                                        · rcases p2834_3 (m.d 2 5) (by simp) with h2843 | h2843
                                          · linarith only [h2631, h2843, hlam]
                                          · rcases p2834_3 (m.d 3 5) (by simp) with h2845 | h2845
                                            · linarith only [h2633, h2845, hlam]
                                            · rcases p2834_3 (m.d 4 5) (by simp) with h2847 | h2847
                                              · linarith only [h2634, h2847, hlam]
                                              · linarith only [h2014, h2847, hlam]
                                        · linarith only [h1407, h2842, hlam]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [hlam, p2834_0]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      rcases p2834_3 (m.d 0 5) (by simp) with h2852 | h2852
                                      · linarith only [h1407, h2852, hlam]
                                      · linarith only [h2011, h2852, hlam]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      rcases p2834_3 (m.d 0 5) (by simp) with h2855 | h2855
                                      · linarith only [h1407, h2855, hlam]
                                      · linarith only [h2013, h2855, hlam]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2010, h2014, h2629, h2632, h2634, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2834_1, u2ehi3]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2011, hlam, p2834_1]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2631, hlam, p2834_1]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [hlam, p2834_0]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2011, h2013, h2629, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2652_1, p2834_1]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2637, hlam, p2834_0]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2013, hlam, p2834_1]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2633, hlam, p2834_1]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2636, hlam, p2834_0]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [hlam, p2834_0]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2639, hlam, p2834_0]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2011, hc45, hlam, hphi, ht23, ht34, p2834_1, u2ehi4]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2634, hlam, p2834_1]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [h2629, h2632, h2634, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2834_1, u2ehi4]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      rcases p2834_3 (m.d 0 5) (by simp) with h2872 | h2872
                                      · linarith only [h2014, h2872, hlam]
                                      · linarith only [h2013, h2872, hlam]
                                    · have p2834_0 := h2834c.1
                                      have p2834_1 := h2834c.2.1
                                      have p2834_2 := h2834c.2.2.1
                                      have p2834_3 := h2834c.2.2.2
                                      linarith only [hlam, p2834_0]
                          · linarith only [h2781, h879, hlam]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2878 | h2878
                        · linarith only [h2878, h879, hlam]
                        · linarith only [h2009, h2878, hlam]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2881 | h2881
                        · linarith only [h2881, h879, hlam]
                        · linarith only [h2012, h2881, hlam]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2884 | h2884
                        · linarith only [h2884, h879, hlam]
                        · linarith only [h2013, h2884, hlam]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2009, hlam, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2629, hlam, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2641_1, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2641_1, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2012, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2632, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2635, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2639, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2013, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2633, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2636, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h0, h2636, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2641_1, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [hlam, p2652_0]
              · linarith only [h2629, h2645, hlam]
            · linarith only [h2644, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            rcases p2641_3 (m.d 0 2) (by simp) with h2904 | h2904
            · rcases p2641_3 (m.d 1 2) (by simp) with h2905 | h2905
              · rcases p2641_3 (m.d 2 3) (by simp) with h2906 | h2906
                · linarith only [h2009, h2906, hlam]
                · linarith only [h2635, h2906, hlam]
              · linarith only [h2630, h2905, hlam]
            · linarith only [h2904, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            rcases p2641_3 (m.d 0 2) (by simp) with h2911 | h2911
            · rcases p2641_3 (m.d 1 2) (by simp) with h2912 | h2912
              · rcases p2641_3 (m.d 2 3) (by simp) with h2913 | h2913
                · linarith only [h2009, h2913, hlam]
                · linarith only [h2636, h2913, hlam]
              · linarith only [h2631, h2912, hlam]
            · linarith only [h2911, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h2009, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2641_1, u2ehi2]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            rcases p2641_3 (m.d 0 2) (by simp) with h2920 | h2920
            · linarith only [h0, h2920, hlam]
            · linarith only [h2009, h2920, hlam]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            rcases p2641_3 (m.d 0 2) (by simp) with h2923 | h2923
            · linarith only [h0, h2923, hlam]
            · linarith only [h2010, h2923, hlam]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            rcases p2641_3 (m.d 0 2) (by simp) with h2926 | h2926
            · linarith only [h0, h2926, hlam]
            · linarith only [h2011, h2926, hlam]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h2009, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h2629, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h2009, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2641_1, u2ehi3]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h0, h2009, h2637, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2641_1, u2ehi3]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h2010, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h2630, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h2635, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h2637, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h2011, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h2631, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [h2636, hlam, p2641_0]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [hc25, hlam, hphi, p2641_1, u2ehi3]
          · have p2641_0 := h2641c.1
            have p2641_1 := h2641c.2.1
            have p2641_2 := h2641c.2.2.1
            have p2641_3 := h2641c.2.2.2
            linarith only [hlam, p2641_0]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2944 | h2944
      · linarith only [h2013, h2014, h2635, h2636, h2944, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h2946 | h2946
        · linarith only [h2013, h2014, h2635, h2636, h2946, hc34, hlam, hphi, ht23, u2ehi3]
        · rcases h2bigk with h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h0, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            rcases p2948_3 (m.d 0 2) (by simp) with h2951 | h2951
            · rcases p2948_3 (m.d 1 2) (by simp) with h2952 | h2952
              · rcases p2948_3 (m.d 2 3) (by simp) with h2953 | h2953
                · linarith only [h2953, hlam, p2948_0]
                · rcases p2948_3 (m.d 2 4) (by simp) with h2955 | h2955
                  · linarith only [h2010, h2955, hlam]
                  · rcases p2948_3 (m.d 2 5) (by simp) with h2957 | h2957
                    · linarith only [h2011, h2957, hlam]
                    · linarith only [h2636, h2957, hlam]
              · linarith only [h2629, h2952, hlam]
            · linarith only [h2951, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            rcases p2948_3 (m.d 0 2) (by simp) with h2962 | h2962
            · rcases p2948_3 (m.d 1 2) (by simp) with h2963 | h2963
              · rcases p2948_3 (m.d 2 3) (by simp) with h2964 | h2964
                · linarith only [h2009, h2964, hlam]
                · linarith only [h2635, h2964, hlam]
              · linarith only [h2630, h2963, hlam]
            · linarith only [h2962, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            rcases p2948_3 (m.d 0 2) (by simp) with h2969 | h2969
            · rcases p2948_3 (m.d 1 2) (by simp) with h2970 | h2970
              · rcases p2948_3 (m.d 2 3) (by simp) with h2971 | h2971
                · linarith only [h2009, h2971, hlam]
                · rcases p2948_3 (m.d 2 4) (by simp) with h2973 | h2973
                  · linarith only [h2010, h2973, hlam]
                  · rcases p2948_3 (m.d 2 5) (by simp) with h2975 | h2975
                    · linarith only [h2975, hlam, p2948_0]
                    · rcases h3bigk with h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c | h2977c
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [hlam, p2977_0]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h879, hlam, p2977_1]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        rcases p2977_3 (m.d 0 3) (by simp) with h2980 | h2980
                        · rcases p2977_3 (m.d 1 3) (by simp) with h2981 | h2981
                          · rcases p2977_3 (m.d 2 3) (by simp) with h2982 | h2982
                            · linarith only [h2009, h2982, hlam]
                            · rcases p2977_3 (m.d 3 4) (by simp) with h2984 | h2984
                              · linarith only [h2012, h2984, hlam]
                              · rcases p2977_3 (m.d 3 5) (by simp) with h2986 | h2986
                                · linarith only [h2013, h2986, hlam]
                                · linarith only [h2636, h2986, hlam]
                          · linarith only [h2629, h2981, hlam]
                        · linarith only [h2009, h2980, hlam]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2013, h2635, h2636, hlam, p2977_2]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2635, h2636, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2977_1, u2ehi3]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2013, h2629, h2635, h2636, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2977_1, u2ehi3]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [hlam, p2977_0]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        rcases p2977_3 (m.d 0 3) (by simp) with h2995 | h2995
                        · linarith only [h2995, h879, hlam]
                        · linarith only [h2009, h2995, hlam]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2013, h2635, h2636, h879, hlam, p2977_2]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2635, h2636, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2977_1, u2ehi3]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2009, hlam, p2977_1]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2629, hlam, p2977_1]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [hlam, p2977_0]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2013, h2636, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2977_1]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2636, hlam, p2977_0]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2012, hlam, p2977_0]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2632, hlam, p2977_0]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2635, hlam, p2977_0]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [hlam, p2977_0]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2946, hlam, p2977_0]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2013, hlam, p2977_0]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2633, hlam, p2977_0]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [h2013, h2014, h2634, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2977_1, u2ehi2]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        rcases p2977_3 (m.d 0 3) (by simp) with h3013 | h3013
                        · rcases p2977_3 (m.d 1 3) (by simp) with h3014 | h3014
                          · rcases p2977_3 (m.d 2 3) (by simp) with h3015 | h3015
                            · linarith only [h2636, h3015, hlam]
                            · linarith only [h2635, h3015, hlam]
                          · linarith only [h2632, h3014, hlam]
                        · linarith only [h2012, h3013, hlam]
                      · have p2977_0 := h2977c.1
                        have p2977_1 := h2977c.2.1
                        have p2977_2 := h2977c.2.2.1
                        have p2977_3 := h2977c.2.2.2
                        linarith only [hlam, p2977_0]
              · linarith only [h2631, h2970, hlam]
            · linarith only [h2969, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2009, h2635, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2948_1, u2ehi3]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            rcases p2948_3 (m.d 0 2) (by simp) with h3025 | h3025
            · linarith only [h0, h3025, hlam]
            · linarith only [h2009, h3025, hlam]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            rcases p2948_3 (m.d 0 2) (by simp) with h3028 | h3028
            · linarith only [h0, h3028, hlam]
            · linarith only [h2010, h3028, hlam]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            rcases p2948_3 (m.d 0 2) (by simp) with h3031 | h3031
            · linarith only [h0, h3031, hlam]
            · linarith only [h2011, h3031, hlam]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2009, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2629, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2009, h2013, h2636, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2948_1, u2ehi3]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2636, hlam, p2948_1]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2010, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2630, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2635, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2944, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2011, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2631, hlam, p2948_0]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [hc25, hlam, hphi, p2948_1, u2ehi2]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [h2013, h2014, h2629, h2632, h2634, h2636, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2948_1, u2ehi3]
          · have p2948_0 := h2948c.1
            have p2948_1 := h2948c.2.1
            have p2948_2 := h2948c.2.2.1
            have p2948_3 := h2948c.2.2.2
            linarith only [hlam, p2948_0]
  · linarith only [h2012, h2014, h2629, h2632, h2634, h2635, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]

end R2N4
