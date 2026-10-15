import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_29S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5254000 in
set_option maxHeartbeats 5254000 in
theorem r1l7_21_15_M_LI_L_I_s1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_21_15_M_LI_L_I_s1_x0 m hb1 hb5 hg0 hg1 h2
  · exact r1l7_21_15_M_LI_L_I_s1_x1 m hb1 hb5 hg0 hg1 h2

set_option maxHeartbeats 6154000 in
set_option maxHeartbeats 6154000 in
theorem r1l7_21_15_M_LI_L_I_s0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_21_15_M_LI_L_I_s1 m hb1 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2629 | h2629
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2630 | h2630
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2631 | h2631
        · linarith only [h0, h1, h2631, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2633 | h2633
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2634 | h2634
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2635 | h2635
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2636 | h2636
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2637 | h2637
                  · linarith only [h2631, h2633, h2637, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2639 | h2639
                    · linarith only [h0, h1, h2639, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2641 | h2641
                      · linarith only [h1, h2629, h2639, h2641, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · linarith only [h0, h1, h2633, h2641, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2644 | h2644
                  · linarith only [h0, h1, h2644, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2646 | h2646
                    · linarith only [h0, h1, h2646, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2648 | h2648
                      · linarith only [h1, h2629, h2646, h2648, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · linarith only [h0, h1, h2633, h2648, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · linarith only [h0, h1, h2633, h2635, hlam]
            · linarith only [h1, h2629, h2634, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2653 | h2653
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2654 | h2654
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2655 | h2655
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2656 | h2656
                  · linarith only [h0, h1, h2656, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2658 | h2658
                    · linarith only [h0, h1, h2658, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2660 | h2660
                      · linarith only [h1, h2629, h2633, h2658, h2660, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2662 | h2662
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2663 | h2663
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2664 | h2664
                            · linarith only [h1, h2629, h2664, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · linarith only [h1, h2629, h2655, h2658, h2664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · linarith only [h0, h1, h2663, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h2629, h2653, h2662, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2669 | h2669
                  · linarith only [h0, h1, h2669, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2671 | h2671
                    · linarith only [h0, h1, h2671, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2673 | h2673
                      · linarith only [h0, h2633, h2673, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2675 | h2675
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2676 | h2676
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2677 | h2677
                            · linarith only [h1, h2629, h2655, h2677, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2679 | h2679
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2680 | h2680
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2681 | h2681
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2682 | h2682
                                    · linarith only [h2629, h2655, h2675, h2682, hlam]
                                    · rcases h1bigk with h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c | h2684c
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2684_1, u1elo2]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h1, hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2684_1, u1elo2]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p2684_1, u1elo2]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h0, hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h2669, hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h2671, hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h2673, hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [hc01, hlam, hphi, p2684_1, u1elo2]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        rcases p2684_3 (m.d 0 1) (by simp) with h2696 | h2696
                                        · linarith only [h1, h2696, hlam]
                                        · linarith only [h0, h2696, hlam]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        rcases p2684_3 (m.d 0 1) (by simp) with h2700 | h2700
                                        · linarith only [h1, h2700, hlam]
                                        · linarith only [h2629, h2700, hlam]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        rcases p2684_3 (m.d 0 1) (by simp) with h2703 | h2703
                                        · linarith only [h1, h2703, hlam]
                                        · linarith only [h2630, h2703, hlam]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h2629, hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h2629, h2655, h2681, hc12, hc24, hlam, hphi, p2684_1]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h2675, hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h2677, hlam, p2684_1]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h2630, hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h1, h2630, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2684_1, u1elo2]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h2676, hlam, p2684_0]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [h1, h2630, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2684_1, u1elo2]
                                      · have p2684_0 := h2684c.1
                                        have p2684_1 := h2684c.2.1
                                        have p2684_2 := h2684c.2.2.1
                                        have p2684_3 := h2684c.2.2.2
                                        linarith only [hlam, p2684_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2716 | h2716
                                    · linarith only [h2671, h2681, h2716, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h1bigk with h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c | h2718c
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2718_1, u1elo2]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h1, hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2718_1, u1elo2]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p2718_1, u1elo2]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h0, hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h2669, hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h2671, hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h2673, hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [hc01, hlam, hphi, p2718_1, u1elo2]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        rcases p2718_3 (m.d 0 1) (by simp) with h2730 | h2730
                                        · linarith only [h1, h2730, hlam]
                                        · linarith only [h0, h2730, hlam]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        rcases p2718_3 (m.d 0 1) (by simp) with h2734 | h2734
                                        · linarith only [h1, h2734, hlam]
                                        · linarith only [h2629, h2734, hlam]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        rcases p2718_3 (m.d 0 1) (by simp) with h2737 | h2737
                                        · linarith only [h1, h2737, hlam]
                                        · linarith only [h2630, h2737, hlam]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h2629, hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h2630, h2677, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2718_1, u1elo0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h2675, hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h2677, hlam, p2718_1]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h2630, hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h1, h2630, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2718_1, u1elo2]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h2676, hlam, p2718_0]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [h1, h2630, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2718_1, u1elo2]
                                      · have p2718_0 := h2718c.1
                                        have p2718_1 := h2718c.2.1
                                        have p2718_2 := h2718c.2.2.1
                                        have p2718_3 := h2718c.2.2.2
                                        linarith only [hlam, p2718_0]
                                · linarith only [h0, h1, h2669, h2680, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h2630, h2669, h2671, h2677, h2679, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1, h2676, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h2675, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h2630, h2654, hlam]
            · linarith only [h1, h2629, h2653, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2756 | h2756
        · linarith only [h0, h1, h2756, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2758 | h2758
          · linarith only [h0, h2630, h2758, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2760 | h2760
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2761 | h2761
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2762 | h2762
                · linarith only [h2629, h2630, h2762, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2764 | h2764
                  · linarith only [h0, h1, h2756, h2764, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2766 | h2766
                    · linarith only [h0, h1, h2766, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2768 | h2768
                      · linarith only [h2629, h2630, h2758, h2766, h2768, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2770 | h2770
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2771 | h2771
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2772 | h2772
                            · linarith only [h2629, h2630, h2762, h2771, h2772, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2774 | h2774
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2775 | h2775
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2776 | h2776
                                  · linarith only [h2629, h2630, h2766, h2772, h2776, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2778 | h2778
                                    · linarith only [h2629, h2630, h2768, h2770, h2776, h2778, hlam]
                                    · rcases h1bigk with h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2630, h2771, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2780_1, u1elo2]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h1, hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2630, h2771, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2780_1, u1elo2]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2630, hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h0, hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2764, hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2766, hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2768, hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [hc01, hlam, hphi, p2780_1, u1elo2]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        rcases p2780_3 (m.d 0 1) (by simp) with h2792 | h2792
                                        · linarith only [h1, h2792, hlam]
                                        · linarith only [h0, h2792, hlam]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        rcases p2780_3 (m.d 0 1) (by simp) with h2796 | h2796
                                        · linarith only [h1, h2796, hlam]
                                        · linarith only [h2629, h2796, hlam]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2629, h2630, h2766, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2780_1, u1elo2]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2629, hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2629, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2780_1, u1elo0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2770, hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2772, hlam, p2780_1]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [hc01, hlam, hphi, p2780_1, u1elo4]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        rcases p2780_3 (m.d 0 1) (by simp) with h2806 | h2806
                                        · linarith only [h2630, h2806, hlam]
                                        · linarith only [h0, h2806, hlam]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [h2771, hlam, p2780_0]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        rcases p2780_3 (m.d 0 1) (by simp) with h2810 | h2810
                                        · linarith only [h2630, h2810, hlam]
                                        · linarith only [h2629, h2810, hlam]
                                      · have p2780_0 := h2780c.1
                                        have p2780_1 := h2780c.2.1
                                        have p2780_2 := h2780c.2.2.1
                                        have p2780_3 := h2780c.2.2.2
                                        linarith only [hlam, p2780_0]
                                · linarith only [h1, h2629, h2761, h2764, h2766, h2775, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h2629, h2630, h2764, h2766, h2771, h2774, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h2761, h2771, hlam]
                        · linarith only [h1, h2629, h2766, h2770, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2818 | h2818
                · linarith only [h2629, h2630, h2818, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2820 | h2820
                  · linarith only [h0, h2630, h2820, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2822 | h2822
                    · linarith only [h0, h2630, h2822, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2824 | h2824
                      · linarith only [h2629, h2630, h2822, h2824, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2826 | h2826
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2827 | h2827
                          · linarith only [h1, h2761, h2827, hc01, hlam, hphi, u1elo2]
                          · linarith only [h1, h2629, h2822, h2827, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h2629, h2822, h2826, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h2629, h2760, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2832 | h2832
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2833 | h2833
        · linarith only [h0, h1, h2833, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2835 | h2835
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2836 | h2836
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2837 | h2837
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2838 | h2838
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2839 | h2839
                  · linarith only [h2833, h2835, h2839, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2841 | h2841
                    · linarith only [h0, h1, h2841, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2843 | h2843
                      · linarith only [h0, h1, h2843, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · linarith only [h0, h1, h2835, h2843, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h0, h2629, h2835, h2838, hlam]
              · linarith only [h0, h2629, h2835, h2836, h2837, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2848 | h2848
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2849 | h2849
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2850 | h2850
                  · linarith only [h2833, h2835, h2850, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2852 | h2852
                    · linarith only [h0, h1, h2852, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2854 | h2854
                      · linarith only [h0, h1, h2854, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · linarith only [h0, h1, h2835, h2854, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h0, h1, h2835, h2836, h2849, hlam]
              · linarith only [h0, h1, h2835, h2848, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2859 | h2859
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2860 | h2860
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2861 | h2861
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2862 | h2862
                  · linarith only [h0, h1, h2862, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2864 | h2864
                    · linarith only [h0, h1, h2864, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2866 | h2866
                      · linarith only [h0, h1, h2835, h2866, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2868 | h2868
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2869 | h2869
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2870 | h2870
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2871 | h2871
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2872 | h2872
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2873 | h2873
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2874 | h2874
                                    · rcases h1bigk with h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c | h2875c
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2629, h2868, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2875_1, u1elo2]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h1, hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2629, hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2629, h2868, hc15, hlam, hphi, ht01, ht0b, ht5b, p2875_1, u1elo2]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h0, hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2862, hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2864, hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2866, hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [hc01, hlam, hphi, p2875_1, u1elo2]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        rcases p2875_3 (m.d 0 1) (by simp) with h2887 | h2887
                                        · linarith only [h1, h2887, hlam]
                                        · linarith only [h0, h2887, hlam]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2629, h2832, h2866, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2875_1, u1elo2]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        rcases p2875_3 (m.d 0 1) (by simp) with h2892 | h2892
                                        · linarith only [h1, h2892, hlam]
                                        · linarith only [h2832, h2892, hlam]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2832, h2866, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2875_1, u1elo3]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        rcases p2875_3 (m.d 0 1) (by simp) with h2896 | h2896
                                        · linarith only [h2629, h2896, hlam]
                                        · linarith only [h0, h2896, hlam]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2868, hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        rcases p2875_3 (m.d 0 1) (by simp) with h2901 | h2901
                                        · linarith only [h2629, h2901, hlam]
                                        · linarith only [h2832, h2901, hlam]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2832, hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2832, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2875_1, u1elo0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2869, hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [h2870, hlam, p2875_0]
                                      · have p2875_0 := h2875c.1
                                        have p2875_1 := h2875c.2.1
                                        have p2875_2 := h2875c.2.2.1
                                        have p2875_3 := h2875c.2.2.2
                                        linarith only [hlam, p2875_0]
                                    · linarith only [h2629, h2832, h2868, h2870, h2874, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                  · linarith only [h2629, h2832, h2864, h2870, h2873, hlam]
                                · linarith only [h0, h2629, h2862, h2868, h2872, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h2629, h2832, h2862, h2866, h2868, h2871, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h2629, h2832, h2866, h2870, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h2629, h2832, h2866, h2868, h2869, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h2832, h2859, h2866, h2868, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h2629, h2832, h2861, hlam]
              · linarith only [h1, h2832, h2860, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2918 | h2918
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2919 | h2919
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2920 | h2920
                  · linarith only [h0, h1, h2833, h2920, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2922 | h2922
                    · linarith only [h0, h1, h2922, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2924 | h2924
                      · linarith only [h0, h2835, h2924, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2926 | h2926
                        · linarith only [h1, h2859, h2926, hc01, hlam, hphi, u1elo2]
                        · linarith only [h1, h2832, h2924, h2926, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h2832, h2859, h2919, hlam]
              · linarith only [h1, h2832, h2918, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h2931 | h2931
        · linarith only [h0, h1, h2931, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2933 | h2933
          · linarith only [h0, h2832, h2933, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2935 | h2935
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2936 | h2936
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2937 | h2937
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2938 | h2938
                  · linarith only [h0, h1, h2931, h2938, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2940 | h2940
                    · linarith only [h0, h1, h2940, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2942 | h2942
                      · linarith only [h0, h2832, h2933, h2942, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2944 | h2944
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2945 | h2945
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2946 | h2946
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2947 | h2947
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2948 | h2948
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2949 | h2949
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2950 | h2950
                                    · rcases h1bigk with h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [hlam, p2951_0]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h2832, h2944, h2946, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2951_1, u1elo2]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h1, hlam, p2951_0]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h2629, hlam, p2951_0]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h2832, hlam, p2951_0]
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
                                        linarith only [h2938, hlam, p2951_0]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h2940, hlam, p2951_0]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h2942, hlam, p2951_0]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [hc01, hlam, hphi, p2951_1, u1elo2]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        rcases p2951_3 (m.d 0 1) (by simp) with h2963 | h2963
                                        · linarith only [h1, h2963, hlam]
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
                                        linarith only [h0, h2629, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2951_1, u1elo2]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h0, h2832, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2951_1, u1elo2]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2951_1, u1elo3]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        rcases p2951_3 (m.d 0 1) (by simp) with h2970 | h2970
                                        · linarith only [h2629, h2970, hlam]
                                        · linarith only [h0, h2970, hlam]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h2944, hlam, p2951_0]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [hlam, p2951_0]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h0, h2832, h2944, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2951_1, u1elo2]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2951_1, u1elo4]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        rcases p2951_3 (m.d 0 1) (by simp) with h2977 | h2977
                                        · linarith only [h2832, h2977, hlam]
                                        · linarith only [h0, h2977, hlam]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h2945, hlam, p2951_0]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [h2946, hlam, p2951_0]
                                      · have p2951_0 := h2951c.1
                                        have p2951_1 := h2951c.2.1
                                        have p2951_2 := h2951c.2.2.1
                                        have p2951_3 := h2951c.2.2.2
                                        linarith only [hlam, p2951_0]
                                    · rcases h1bigk with h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2983_1, u1elo2]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h1, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2629, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2832, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h0, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2938, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2940, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2942, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [hc01, hlam, hphi, p2983_1, u1elo2]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        rcases p2983_3 (m.d 0 1) (by simp) with h2995 | h2995
                                        · linarith only [h1, h2995, hlam]
                                        · linarith only [h0, h2995, hlam]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h0, h2629, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2983_1, u1elo2]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h0, h2832, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2983_1, u1elo2]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2983_1, u1elo3]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        rcases p2983_3 (m.d 0 1) (by simp) with h3002 | h3002
                                        · linarith only [h2629, h3002, hlam]
                                        · linarith only [h0, h3002, hlam]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2944, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h0, h2832, h2944, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2983_1, u1elo2]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2983_1, u1elo4]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        rcases p2983_3 (m.d 0 1) (by simp) with h3009 | h3009
                                        · linarith only [h2832, h3009, hlam]
                                        · linarith only [h0, h3009, hlam]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2945, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2946, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [hlam, p2983_0]
                                  · linarith only [h0, h1, h2629, h2935, h2937, h2940, h2949, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                                · linarith only [h0, h1, h2938, h2948, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h2938, h2947, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h2629, h2935, h2937, h2946, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h1, h2936, h2945, hlam]
                        · linarith only [h1, h2935, h2944, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3021 | h3021
                  · linarith only [h0, h2629, h3021, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3023 | h3023
                    · linarith only [h0, h2629, h3023, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3025 | h3025
                      · linarith only [h0, h2629, h3025, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3027 | h3027
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3028 | h3028
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3029 | h3029
                            · linarith only [h0, h2629, h2937, h3027, h3029, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · linarith only [h0, h2629, h3029, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1, h2936, h3028, hlam]
                        · linarith only [h0, h1, h3027, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3034 | h3034
                · linarith only [h2935, h2936, h3034, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3036 | h3036
                  · linarith only [h0, h1, h3036, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3038 | h3038
                    · linarith only [h0, h1, h3038, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3040 | h3040
                      · linarith only [h0, h1, h3040, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3042 | h3042
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3043 | h3043
                          · linarith only [h2935, h2936, h3043, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · linarith only [h0, h2629, h3042, h3043, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h3042, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3047 | h3047
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3048 | h3048
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3049 | h3049
                  · linarith only [h0, h1, h3049, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3051 | h3051
                    · linarith only [h0, h1, h3051, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3053 | h3053
                      · linarith only [h0, h1, h3053, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3055 | h3055
                        · linarith only [h2832, h2935, h3047, h3055, hc01, hlam, hphi, u1elo2]
                        · linarith only [h0, h1, h3055, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h2935, h3047, h3048, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3059 | h3059
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3060 | h3060
                  · linarith only [h0, h1, h3060, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3062 | h3062
                    · linarith only [h0, h2832, h3062, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3064 | h3064
                      · linarith only [h0, h2832, h3064, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3066 | h3066
                        · linarith only [h1, h2935, h3066, hc01, hlam, hphi, u1elo2]
                        · linarith only [h0, h1, h3066, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3069 | h3069
                  · linarith only [h0, h1, h2931, h3069, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3071 | h3071
                    · linarith only [h0, h1, h3071, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3073 | h3073
                      · linarith only [h0, h1, h2933, h3059, h3073, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3075 | h3075
                        · linarith only [h1, h2935, h3075, hc01, hlam, hphi, u1elo2]
                        · linarith only [h0, h1, h3075, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 10528000 in
set_option maxHeartbeats 10528000 in
theorem r1l7_21_15_M_LI_L_I_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  exact r1l7_21_15_M_LI_L_I_s0 m hb1 hb5 h0

set_option maxHeartbeats 10528000 in
set_option maxHeartbeats 10528000 in
theorem r1l7_21_15_M_LI_L_I_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3078 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h3079 | h3079
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3080 | h3080
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3081 | h3081
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3082 | h3082
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3083 | h3083
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3084 | h3084
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3085 | h3085
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3086 | h3086
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3087 | h3087
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3088 | h3088
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3089 | h3089
                      · linarith only [h0, h3078, h3089, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3078, h3083, h3089, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h3079, h3082, h3088, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h3079, h3087, hlam]
                · linarith only [h0, h3079, h3081, h3086, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3095 | h3095
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3096 | h3096
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3097 | h3097
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3098 | h3098
                      · linarith only [h0, h3078, h3098, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3078, h3083, h3098, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h3082, h3097, hlam]
                  · linarith only [h0, h3079, h3096, hlam]
                · linarith only [h0, h3081, h3095, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3104 | h3104
              · linarith only [h3083, h3084, h3104, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3106 | h3106
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3107 | h3107
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3108 | h3108
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3109 | h3109
                      · linarith only [h0, h3078, h3109, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3080, h3083, h3084, h3106, h3109, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h3082, h3108, hlam]
                  · linarith only [h0, h3079, h3107, hlam]
                · linarith only [h0, h3081, h3106, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3115 | h3115
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3116 | h3116
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3117 | h3117
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3118 | h3118
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3119 | h3119
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3120 | h3120
                      · linarith only [h3083, h3115, h3120, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3122 | h3122
                        · linarith only [h0, h3079, h3120, h3122, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h0, h3079, h3083, h3115, h3117, h3122, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h3082, h3119, hlam]
                  · linarith only [h0, h3079, h3118, hlam]
                · linarith only [h0, h3081, h3117, hlam]
              · linarith only [h3083, h3115, h3116, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3129 | h3129
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3130 | h3130
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3131 | h3131
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3132 | h3132
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3133 | h3133
                      · linarith only [h0, h3078, h3133, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3135 | h3135
                        · linarith only [h0, h3079, h3115, h3133, h3135, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3137 | h3137
                          · linarith only [h0, h3079, h3137, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h0, h3079, h3129, h3137, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · linarith only [h0, h3082, h3132, hlam]
                  · linarith only [h0, h3079, h3131, hlam]
                · linarith only [h0, h3081, h3130, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3143 | h3143
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3144 | h3144
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3145 | h3145
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3146 | h3146
                      · linarith only [h3078, h3083, h3146, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3148 | h3148
                        · linarith only [h3078, h3115, h3148, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3150 | h3150
                          · linarith only [h0, h3079, h3129, h3150, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3152 | h3152
                            · linarith only [h3078, h3083, h3143, h3152, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3154 | h3154
                              · linarith only [h0, h3080, h3115, h3143, h3146, h3150, h3154, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3156 | h3156
                                · linarith only [h3079, h3129, h3143, h3144, h3146, h3156, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3158 | h3158
                                  · rcases h1bigk with h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, h3143, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3159_1, u1elo1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, h3143, h3146, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3159_1, u1elo1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, h3143, h3146, h3150, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3159_1, u1elo1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [hc01, hlam, hphi, p3159_1, u1elo1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      rcases p3159_3 (m.d 0 1) (by simp) with h3167 | h3167
                                      · linarith only [h0, h3167, hlam]
                                      · linarith only [h3078, h3167, hlam]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      rcases p3159_3 (m.d 0 1) (by simp) with h3170 | h3170
                                      · linarith only [h0, h3170, hlam]
                                      · linarith only [h3079, h3170, hlam]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      rcases p3159_3 (m.d 0 1) (by simp) with h3173 | h3173
                                      · linarith only [h0, h3173, hlam]
                                      · linarith only [h3080, h3173, hlam]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3078, hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3143, hlam, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3146, hlam, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3148, hlam, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3079, hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3144, hlam, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3079, h3129, h3143, h3158, hc23, hc34, hlam, hphi, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3150, hlam, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3080, hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3145, hlam, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, h3080, h3143, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3159_1, u1elo1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, h3080, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3159_1, u1elo1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [hlam, p3159_0]
                                  · rcases h1bigk with h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c | h3191c
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [hlam, p3191_0]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h0, hlam, p3191_0]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h0, h3143, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3191_1, u1elo1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h0, h3143, h3146, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3191_1, u1elo1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p3191_1, u1elo1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [hc01, hlam, hphi, p3191_1, u1elo1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [hlam, p3191_0]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      rcases p3191_3 (m.d 0 1) (by simp) with h3199 | h3199
                                      · linarith only [h0, h3199, hlam]
                                      · linarith only [h3078, h3199, hlam]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      rcases p3191_3 (m.d 0 1) (by simp) with h3202 | h3202
                                      · linarith only [h0, h3202, hlam]
                                      · linarith only [h3079, h3202, hlam]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      rcases p3191_3 (m.d 0 1) (by simp) with h3205 | h3205
                                      · linarith only [h0, h3205, hlam]
                                      · linarith only [h3080, h3205, hlam]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h3078, hlam, p3191_0]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h3143, hlam, p3191_1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [hlam, p3191_0]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h3146, hlam, p3191_1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h3148, hlam, p3191_1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h3079, hlam, p3191_0]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h3144, hlam, p3191_1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h3080, h3143, h3150, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3191_1, u1elo0]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [hlam, p3191_0]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h3150, hlam, p3191_1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h3080, hlam, p3191_0]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h3145, hlam, p3191_1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h0, h3080, h3143, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3191_1, u1elo1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [h0, h3080, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3191_1, u1elo1]
                                    · have p3191_0 := h3191c.1
                                      have p3191_1 := h3191c.2.1
                                      have p3191_2 := h3191c.2.2.1
                                      have p3191_3 := h3191c.2.2.2
                                      linarith only [hlam, p3191_0]
                    · linarith only [h0, h3080, h3082, h3145, hlam]
                  · linarith only [h0, h3079, h3144, hlam]
                · linarith only [h0, h3081, h3143, hlam]
        · linarith only [h0, h3080, h3082, hlam]
      · linarith only [h0, h3078, h3081, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3228 | h3228
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3229 | h3229
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3230 | h3230
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3231 | h3231
            · linarith only [h3078, h3080, h3231, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3233 | h3233
              · linarith only [h3078, h3080, h3230, h3233, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3235 | h3235
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3236 | h3236
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3237 | h3237
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3238 | h3238
                      · linarith only [h3078, h3080, h3237, h3238, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h3078, h3080, h3230, h3235, h3237, h3238, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h3079, h3229, h3236, h3237, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h3079, h3236, hlam]
                · linarith only [h0, h3228, h3235, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3244 | h3244
            · linarith only [h3078, h3080, h3244, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3246 | h3246
              · linarith only [h3079, h3080, h3246, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3248 | h3248
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3249 | h3249
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3250 | h3250
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3251 | h3251
                      · linarith only [h3078, h3080, h3230, h3250, h3251, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3253 | h3253
                        · linarith only [h3078, h3080, h3244, h3253, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3255 | h3255
                          · linarith only [h3079, h3246, h3255, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3257 | h3257
                            · linarith only [h0, h3228, h3230, h3257, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3259 | h3259
                              · linarith only [h3080, h3248, h3253, h3259, hc01, hlam, hphi, u1elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3261 | h3261
                                · linarith only [h3079, h3080, h3249, h3255, h3261, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3263 | h3263
                                  · linarith only [h3079, h3080, h3249, h3255, h3257, h3263, hc23, hc34, hlam, hphi]
                                  · rcases h1bigk with h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c | h3265c
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [hlam, p3265_0]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h0, hlam, p3265_0]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3080, h3250, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3265_1, u1elo1]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3080, h3250, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3265_1, u1elo1]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3080, hlam, p3265_0]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [hc01, hlam, hphi, p3265_1, u1elo1]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [hlam, p3265_0]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      rcases p3265_3 (m.d 0 1) (by simp) with h3273 | h3273
                                      · linarith only [h0, h3273, hlam]
                                      · linarith only [h3078, h3273, hlam]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      rcases p3265_3 (m.d 0 1) (by simp) with h3276 | h3276
                                      · linarith only [h0, h3276, hlam]
                                      · linarith only [h3079, h3276, hlam]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3079, h3080, h3249, h3257, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3265_1, u1elo1]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3078, hlam, p3265_0]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3248, hlam, p3265_1]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [hlam, p3265_0]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3251, hlam, p3265_1]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3253, hlam, p3265_1]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3079, hlam, p3265_0]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3249, hlam, p3265_1]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3079, h3080, h3248, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3265_1, u1elo4]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [hlam, p3265_0]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3255, hlam, p3265_1]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [hc01, hlam, hphi, p3265_1, u1elo4]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [h3250, hlam, p3265_1]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      rcases p3265_3 (m.d 0 1) (by simp) with h3292 | h3292
                                      · linarith only [h3080, h3292, hlam]
                                      · linarith only [h3078, h3292, hlam]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      rcases p3265_3 (m.d 0 1) (by simp) with h3295 | h3295
                                      · linarith only [h3080, h3295, hlam]
                                      · linarith only [h3079, h3295, hlam]
                                    · have p3265_0 := h3265c.1
                                      have p3265_1 := h3265c.2.1
                                      have p3265_2 := h3265c.2.2.1
                                      have p3265_3 := h3265c.2.2.2
                                      linarith only [hlam, p3265_0]
                    · linarith only [h0, h3080, h3229, h3250, hc01, hlam, hphi, u1elo4]
                  · linarith only [h0, h3079, h3249, hlam]
                · linarith only [h0, h3228, h3248, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3302 | h3302
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3303 | h3303
            · linarith only [h0, h3078, h3229, h3303, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3305 | h3305
              · linarith only [h0, h3078, h3229, h3302, h3305, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3307 | h3307
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3308 | h3308
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3309 | h3309
                    · linarith only [h0, h3078, h3229, h3307, h3309, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3311 | h3311
                      · linarith only [h0, h3078, h3309, h3311, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h3078, h3302, h3309, h3311, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h3079, h3308, hlam]
                · linarith only [h0, h3079, h3228, h3229, h3307, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3316 | h3316
            · linarith only [h3079, h3080, h3302, h3316, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3318 | h3318
              · linarith only [h0, h3079, h3229, h3318, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3320 | h3320
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3321 | h3321
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3322 | h3322
                    · linarith only [h0, h3078, h3229, h3320, h3322, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3324 | h3324
                      · linarith only [h3078, h3302, h3324, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3326 | h3326
                        · linarith only [h0, h3078, h3316, h3322, h3326, hc05, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3328 | h3328
                          · linarith only [h0, h3079, h3322, h3328, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3330 | h3330
                            · linarith only [h3228, h3302, h3330, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3332 | h3332
                              · linarith only [h0, h3078, h3320, h3322, h3326, h3332, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h3079, h3322, h3324, h3332, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h3079, h3321, hlam]
                · linarith only [h0, h3078, h3228, h3229, h3320, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h3078, h3228, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3338 | h3338
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3339 | h3339
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3340 | h3340
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3341 | h3341
          · linarith only [h3078, h3079, h3341, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3343 | h3343
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3344 | h3344
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3345 | h3345
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3346 | h3346
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3347 | h3347
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3348 | h3348
                      · linarith only [h3078, h3079, h3341, h3348, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3350 | h3350
                        · linarith only [h3078, h3079, h3346, h3350, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h3078, h3079, h3343, h3346, h3350, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h3079, h3338, h3340, h3346, h3347, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3354 | h3354
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3355 | h3355
                      · linarith only [h3078, h3341, h3343, h3355, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3357 | h3357
                        · linarith only [h0, h3078, h3346, h3357, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h3078, h3343, h3346, h3357, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h3340, h3354, hlam]
                · linarith only [h0, h3339, h3345, hlam]
              · linarith only [h3078, h3079, h3343, h3344, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3363 | h3363
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3364 | h3364
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3365 | h3365
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3366 | h3366
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3367 | h3367
                      · linarith only [h3078, h3079, h3341, h3365, h3367, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3369 | h3369
                        · linarith only [h3078, h3079, h3343, h3365, h3369, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3371 | h3371
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3372 | h3372
                            · linarith only [h0, h3079, h3338, h3339, h3367, h3369, h3372, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3374 | h3374
                              · linarith only [h3079, h3338, h3364, h3369, h3374, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3376 | h3376
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3377 | h3377
                                  · rcases h1bigk with h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [hlam, p3378_0]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h0, hlam, p3378_0]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3079, h3365, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3378_1, u1elo1]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3079, hlam, p3378_0]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3079, h3365, hc15, hlam, hphi, ht01, ht0b, ht5b, p3378_1, u1elo1]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [hc01, hlam, hphi, p3378_1, u1elo1]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [hlam, p3378_0]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      rcases p3378_3 (m.d 0 1) (by simp) with h3386 | h3386
                                      · linarith only [h0, h3386, hlam]
                                      · linarith only [h3078, h3386, hlam]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3079, h3338, h3366, h3374, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3378_1, u1elo1]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      rcases p3378_3 (m.d 0 1) (by simp) with h3390 | h3390
                                      · linarith only [h0, h3390, hlam]
                                      · linarith only [h3338, h3390, hlam]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3078, hlam, p3378_0]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3364, hlam, p3378_1]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [hlam, p3378_0]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3367, hlam, p3378_1]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3369, hlam, p3378_1]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3338, h3366, h3374, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3378_1, u1elo3]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3365, hlam, p3378_1]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      rcases p3378_3 (m.d 0 1) (by simp) with h3400 | h3400
                                      · linarith only [h3079, h3400, hlam]
                                      · linarith only [h3078, h3400, hlam]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [hlam, p3378_0]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      rcases p3378_3 (m.d 0 1) (by simp) with h3404 | h3404
                                      · linarith only [h3079, h3404, hlam]
                                      · linarith only [h3338, h3404, hlam]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3338, hlam, p3378_0]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3366, hlam, p3378_1]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3338, h3364, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3378_1, u1elo0]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [h3371, hlam, p3378_0]
                                    · have p3378_0 := h3378c.1
                                      have p3378_1 := h3378c.2.1
                                      have p3378_2 := h3378c.2.2.1
                                      have p3378_3 := h3378c.2.2.2
                                      linarith only [hlam, p3378_0]
                                  · linarith only [h3078, h3079, h3364, h3367, h3377, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h3079, h3338, h3365, h3371, h3376, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h3079, h3338, h3364, h3369, h3371, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h3340, h3366, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3416 | h3416
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3417 | h3417
                      · linarith only [h0, h3078, h3365, h3417, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3419 | h3419
                        · linarith only [h0, h3078, h3365, h3419, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3421 | h3421
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3422 | h3422
                            · linarith only [h0, h3338, h3364, h3365, h3417, h3419, h3422, hlam]
                            · linarith only [h0, h3338, h3365, h3419, h3422, hc13, hc34, hlam, hphi]
                          · linarith only [h0, h3338, h3364, h3365, h3419, h3421, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h3340, h3416, hlam]
                · linarith only [h0, h3339, h3364, hlam]
              · linarith only [h3079, h3338, h3363, hlam]
        · linarith only [h0, h3338, h3340, hlam]
      · linarith only [h0, h3078, h3339, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3431 | h3431
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3432 | h3432
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3433 | h3433
          · linarith only [h3078, h3079, h3433, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3435 | h3435
            · linarith only [h3078, h3338, h3435, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3437 | h3437
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3438 | h3438
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3439 | h3439
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3440 | h3440
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3441 | h3441
                      · linarith only [h3078, h3338, h3433, h3441, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3443 | h3443
                        · linarith only [h3078, h3338, h3435, h3443, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3445 | h3445
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3446 | h3446
                            · linarith only [h3078, h3338, h3431, h3441, h3445, h3446, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3448 | h3448
                              · linarith only [h3078, h3338, h3438, h3443, h3448, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3450 | h3450
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3451 | h3451
                                  · rcases h1bigk with h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [hlam, p3452_0]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h0, hlam, p3452_0]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3338, h3438, h3445, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3452_1, u1elo3]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3079, hlam, p3452_0]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3338, hlam, p3452_0]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [hc01, hlam, hphi, p3452_1, u1elo1]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [hlam, p3452_0]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      rcases p3452_3 (m.d 0 1) (by simp) with h3460 | h3460
                                      · linarith only [h0, h3460, hlam]
                                      · linarith only [h3078, h3460, hlam]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3078, h3079, h3438, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3452_1, u1elo1]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3078, h3338, h3438, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3452_1, u1elo1]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3078, hlam, p3452_0]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3438, hlam, p3452_1]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [hlam, p3452_0]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3441, hlam, p3452_1]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3443, hlam, p3452_1]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3078, h3438, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3452_1, u1elo3]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3439, hlam, p3452_1]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      rcases p3452_3 (m.d 0 1) (by simp) with h3472 | h3472
                                      · linarith only [h3079, h3472, hlam]
                                      · linarith only [h3078, h3472, hlam]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [hlam, p3452_0]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3078, h3338, h3438, h3439, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3452_1, u1elo1]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3078, h3438, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3452_1, u1elo4]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3440, hlam, p3452_1]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      rcases p3452_3 (m.d 0 1) (by simp) with h3479 | h3479
                                      · linarith only [h3338, h3479, hlam]
                                      · linarith only [h3078, h3479, hlam]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [h3445, hlam, p3452_0]
                                    · have p3452_0 := h3452c.1
                                      have p3452_1 := h3452c.2.1
                                      have p3452_2 := h3452c.2.2.1
                                      have p3452_3 := h3452c.2.2.2
                                      linarith only [hlam, p3452_0]
                                  · linarith only [h3078, h3079, h3437, h3438, h3441, h3451, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3485 | h3485
                                  · rcases h1bigk with h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c | h3486c
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [hlam, p3486_0]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h0, hlam, p3486_0]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3338, h3438, h3445, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3486_1, u1elo3]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3079, hlam, p3486_0]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3338, hlam, p3486_0]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [hc01, hlam, hphi, p3486_1, u1elo1]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [hlam, p3486_0]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      rcases p3486_3 (m.d 0 1) (by simp) with h3494 | h3494
                                      · linarith only [h0, h3494, hlam]
                                      · linarith only [h3078, h3494, hlam]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3079, h3437, h3450, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3486_1, u1elo1]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3078, h3338, h3438, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3486_1, u1elo1]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3078, hlam, p3486_0]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3438, hlam, p3486_1]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [hlam, p3486_0]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3441, hlam, p3486_1]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3443, hlam, p3486_1]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3078, h3438, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3486_1, u1elo3]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3439, hlam, p3486_1]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      rcases p3486_3 (m.d 0 1) (by simp) with h3506 | h3506
                                      · linarith only [h3079, h3506, hlam]
                                      · linarith only [h3078, h3506, hlam]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [hlam, p3486_0]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3078, h3338, h3438, h3439, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3486_1, u1elo1]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3078, h3438, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3486_1, u1elo4]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3440, hlam, p3486_1]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      rcases p3486_3 (m.d 0 1) (by simp) with h3513 | h3513
                                      · linarith only [h3338, h3513, hlam]
                                      · linarith only [h3078, h3513, hlam]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [h3445, hlam, p3486_0]
                                    · have p3486_0 := h3486c.1
                                      have p3486_1 := h3486c.2.1
                                      have p3486_2 := h3486c.2.2.1
                                      have p3486_3 := h3486c.2.2.2
                                      linarith only [hlam, p3486_0]
                                  · linarith only [h3078, h3079, h3437, h3438, h3441, h3485, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h3079, h3437, h3445, hlam]
                    · linarith only [h0, h3078, h3338, h3432, h3438, h3440, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3521 | h3521
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3522 | h3522
                      · linarith only [h3078, h3338, h3439, h3521, h3522, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3524 | h3524
                        · linarith only [h3078, h3338, h3439, h3521, h3524, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3526 | h3526
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3527 | h3527
                            · linarith only [h3078, h3338, h3438, h3439, h3521, h3522, h3527, hlam]
                            · linarith only [h3078, h3338, h3438, h3439, h3521, h3527, hc23, hc34, hlam, hphi]
                          · linarith only [h3078, h3338, h3438, h3439, h3521, h3526, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h3432, h3521, hlam]
                · linarith only [h0, h3431, h3438, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3533 | h3533
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3534 | h3534
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3535 | h3535
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3536 | h3536
                      · linarith only [h3078, h3338, h3536, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3538 | h3538
                        · linarith only [h3078, h3079, h3534, h3538, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3540 | h3540
                          · linarith only [h3078, h3079, h3437, h3533, h3534, h3540, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h3078, h3079, h3533, h3540, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h3432, h3535, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3544 | h3544
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3545 | h3545
                      · linarith only [h0, h3078, h3534, h3545, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3547 | h3547
                        · linarith only [h3078, h3338, h3534, h3544, h3547, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3549 | h3549
                          · linarith only [h3079, h3437, h3549, hc01, hlam, hphi, u1elo3]
                          · linarith only [h3078, h3079, h3533, h3549, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h3432, h3544, hlam]
                · linarith only [h0, h3431, h3533, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3554 | h3554
          · linarith only [h3078, h3079, h3554, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3556 | h3556
            · linarith only [h0, h3078, h3432, h3556, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3558 | h3558
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3559 | h3559
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3560 | h3560
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3561 | h3561
                    · linarith only [h0, h3078, h3432, h3559, h3561, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3563 | h3563
                      · linarith only [h3078, h3079, h3554, h3563, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3565 | h3565
                        · linarith only [h0, h3078, h3432, h3556, h3565, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3567 | h3567
                          · linarith only [h3560, h3561, h3567, hlam]
                          · linarith only [h3078, h3079, h3558, h3567, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3570 | h3570
                    · linarith only [h0, h3078, h3432, h3559, h3560, h3570, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3572 | h3572
                      · linarith only [h0, h3078, h3560, h3572, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3574 | h3574
                        · linarith only [h0, h3078, h3560, h3574, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3576 | h3576
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3577 | h3577
                            · linarith only [h0, h3078, h3559, h3570, h3572, h3576, h3577, hlam]
                            · linarith only [h0, h3078, h3559, h3560, h3577, hc23, hc34, hlam, hphi]
                          · linarith only [h3079, h3558, h3576, hlam]
                · linarith only [h0, h3431, h3559, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3582 | h3582
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3583 | h3583
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3584 | h3584
                    · linarith only [h0, h3078, h3432, h3582, h3584, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3586 | h3586
                      · linarith only [h3078, h3079, h3586, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3588 | h3588
                        · linarith only [h3078, h3079, h3583, h3584, h3588, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3590 | h3590
                          · linarith only [h3079, h3558, h3583, h3584, h3590, hc01, hc25, hlam, hphi, ht12]
                          · linarith only [h3078, h3079, h3582, h3590, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3593 | h3593
                    · linarith only [h0, h3078, h3432, h3582, h3593, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3595 | h3595
                      · linarith only [h0, h3078, h3583, h3595, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3597 | h3597
                        · linarith only [h0, h3078, h3583, h3597, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3599 | h3599
                          · linarith only [h3078, h3079, h3558, h3582, h3599, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                          · linarith only [h0, h3078, h3582, h3583, h3599, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h3078, h3431, h3582, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h3078, h3431, hlam]

end R2N4
