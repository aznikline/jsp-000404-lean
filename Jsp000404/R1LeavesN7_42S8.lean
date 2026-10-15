import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_42S5
import Jsp000404.R1LeavesN7_42S6
import Jsp000404.R1LeavesN7_42S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1180 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1692 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1845 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1989 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2657 | h2657
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2658 | h2658
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2659 | h2659
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2660 | h2660
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2661 | h2661
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2662 | h2662
            · linarith only [h1989, h2657, h2662, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2664 | h2664
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2665 | h2665
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2666 | h2666
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2667 | h2667
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2668 | h2668
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2669 | h2669
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2670 | h2670
                          · linarith only [h2657, h2670, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                          · linarith only [h2661, h2670, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                        · linarith only [h1692, h2661, h2662, h2664, h2669, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h1692, h2661, h2662, h2664, h2668, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h1692, h2661, h2667, hlam]
                  · linarith only [h1180, h2659, h2666, hlam]
                · linarith only [h0, h2658, h2665, hlam]
              · linarith only [h0, h2657, h2664, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2679 | h2679
            · linarith only [h1989, h2657, h2679, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2681 | h2681
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2682 | h2682
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2683 | h2683
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2684 | h2684
                    · linarith only [h2661, h2679, h2681, h2684, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2686 | h2686
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2687 | h2687
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2688 | h2688
                          · linarith only [h2657, h2684, h2688, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2690 | h2690
                            · linarith only [h0, h1692, h2658, h2679, h2684, h2686, h2688, h2690, hc01, hc23, hlam, hphi, ht12]
                            · rcases h0bigk with h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c | h2692c
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [hlam, p2692_0]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h0, hlam, p2692_1]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h1180, hlam, p2692_0]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h1692, hlam, p2692_1]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h1845, hlam, p2692_1]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h0, h2679, hc01, hc23, hlam, hphi, ht12, p2692_1]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [hlam, p2692_0]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h1989, hlam, p2692_0]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h0, h2657, h2679, h2686, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2692_1, u4ehi3]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h0, h1845, h2679, hc01, hc23, hlam, hphi, ht12, p2692_1]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                rcases p2692_3 (m.d 0 1) (by simp) with h2703 | h2703
                                · linarith only [h1180, h2703, hlam]
                                · rcases p2692_3 (m.d 0 2) (by simp) with h2705 | h2705
                                  · linarith only [h1989, h2705, hlam]
                                  · linarith only [h0, h2705, hlam]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h2658, hc25, hlam, hphi, ht0b, ht5b, p2692_1, u0elo2]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [hlam, p2692_0]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h2657, h2686, hlam, hphi, ht0b, ht45, ht5b, p2692_1, u0elo2, u4ehi3]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h2657, h2661, h2686, hlam, hphi, ht0b, ht45, ht5b, p2692_1, u0elo2, u4ehi3]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h1692, h2684, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2692_1]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h2657, hlam, p2692_0]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h2659, hlam, p2692_0]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [hlam, p2692_0]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h2661, hlam, p2692_0]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h0, h2658, h2679, hc01, hc23, hlam, hphi, ht12, p2692_1]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h2658, hlam, p2692_1]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h2660, hlam, p2692_0]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [h0, h2658, h2679, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2692_1, u4ehi0]
                              · have p2692_0 := h2692c.1
                                have p2692_1 := h2692c.2.1
                                have p2692_2 := h2692c.2.2.1
                                have p2692_3 := h2692c.2.2.2
                                linarith only [hlam, p2692_0]
                        · linarith only [h0, h2679, h2687, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h2657, h2679, h2686, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · linarith only [h1180, h1989, h2657, h2659, h2683, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                · linarith only [h0, h2658, h2682, hlam]
              · linarith only [h0, h2657, h2681, hlam]
        · linarith only [h1989, h2658, h2660, hlam]
      · linarith only [h1989, h2657, h2659, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2729 | h2729
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2730 | h2730
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2731 | h2731
          · linarith only [h2657, h2658, h2731, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2733 | h2733
            · linarith only [h1989, h2657, h2733, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2735 | h2735
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2736 | h2736
                · linarith only [h2657, h2658, h2736, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2738 | h2738
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2739 | h2739
                    · linarith only [h2731, h2733, h2735, h2739, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2741 | h2741
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2742 | h2742
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2743 | h2743
                          · linarith only [h2657, h2739, h2743, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                          · linarith only [h0, h2657, h2736, h2743, hc45, hlam, hphi, u4ehi2]
                        · linarith only [h1180, h2730, h2733, h2742, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h2657, h2729, h2733, h2741, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                  · linarith only [h1180, h2729, h2738, hlam]
              · linarith only [h0, h2657, h2735, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2750 | h2750
          · linarith only [h2657, h2658, h2750, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2752 | h2752
            · linarith only [h1989, h2657, h2752, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2754 | h2754
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2755 | h2755
                · linarith only [h2657, h2658, h2752, h2755, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2757 | h2757
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2758 | h2758
                    · linarith only [h1989, h2657, h2730, h2750, h2752, h2754, h2758, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2760 | h2760
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2761 | h2761
                        · linarith only [h1989, h2657, h2730, h2760, h2761, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h2752, h2761, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h2657, h2752, h2760, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h2657, h2729, h2752, h2757, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
              · linarith only [h0, h2657, h2754, hlam]
      · linarith only [h1989, h2657, h2729, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2768 | h2768
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2769 | h2769
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2770 | h2770
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2771 | h2771
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2772 | h2772
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2773 | h2773
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2774 | h2774
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2775 | h2775
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2776 | h2776
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2777 | h2777
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2778 | h2778
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2779 | h2779
                          · linarith only [h2657, h2768, h2772, h2777, h2779, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h2657, h2769, h2771, h2779, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1989, h2770, h2778, hlam]
                      · linarith only [h1989, h2769, h2777, hlam]
                    · linarith only [h1692, h1989, h2768, h2771, h2772, h2776, hc01, hc13, hlam, hphi]
                  · linarith only [h1989, h2768, h2769, h2771, h2772, h2775, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                · linarith only [h1989, h2769, h2772, h2774, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h1989, h2768, h2771, h2772, h2773, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2788 | h2788
              · linarith only [h2657, h2768, h2771, h2772, h2788, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2790 | h2790
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2791 | h2791
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2792 | h2792
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2793 | h2793
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2794 | h2794
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2795 | h2795
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2796 | h2796
                            · linarith only [h2769, h2796, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                            · linarith only [h2768, h2795, h2796, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                          · linarith only [h1845, h2771, h2788, h2790, h2795, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                        · linarith only [h1180, h2770, h2772, h2794, hlam]
                      · linarith only [h0, h2769, h2772, h2793, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1692, h2771, h2792, hlam]
                  · linarith only [h1180, h2769, h2791, hlam]
                · linarith only [h0, h2768, h2790, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h2657, h2768, h2771, hlam]
        · linarith only [h2657, h2768, h2769, h2770, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2807 | h2807
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2808 | h2808
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2809 | h2809
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2810 | h2810
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2811 | h2811
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2812 | h2812
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2813 | h2813
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2814 | h2814
                      · linarith only [h1989, h2768, h2769, h2809, h2814, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h1989, h2768, h2808, h2809, h2812, h2814, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h2808, h2813, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2818 | h2818
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2819 | h2819
                      · linarith only [h2809, h2812, h2819, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2821 | h2821
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2822 | h2822
                          · linarith only [h1989, h2768, h2809, h2812, h2822, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h2657, h2808, h2822, hlam]
                        · linarith only [h1989, h2768, h2807, h2808, h2821, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                    · linarith only [h1989, h2768, h2808, h2809, h2812, h2818, hlam]
                · linarith only [h1989, h2768, h2811, hc12, hc23, hlam, hphi]
              · linarith only [h1989, h2809, h2810, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2829 | h2829
              · linarith only [h2657, h2768, h2808, h2809, h2829, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2831 | h2831
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2832 | h2832
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2833 | h2833
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2834 | h2834
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2835 | h2835
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2836 | h2836
                          · linarith only [h1989, h2768, h2769, h2809, h2832, h2836, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h2808, h2829, h2836, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                        · linarith only [h1989, h2768, h2769, h2808, h2809, h2832, h2835, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h2809, h2832, h2834, hlam]
                    · linarith only [h1989, h2768, h2769, h2808, h2832, h2833, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2842 | h2842
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2843 | h2843
                      · linarith only [h1845, h2809, h2831, h2832, h2843, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h1845, h2809, h2831, h2843, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h1692, h2768, h2808, h2809, h2842, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h2768, h2831, hlam]
          · linarith only [h1989, h2768, h2769, h2808, hlam]
        · linarith only [h1989, h2768, h2807, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2850 | h2850
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2851 | h2851
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2852 | h2852
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2853 | h2853
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2854 | h2854
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2855 | h2855
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2856 | h2856
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2857 | h2857
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2858 | h2858
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2859 | h2859
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2860 | h2860
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2861 | h2861
                            · linarith only [h2850, h2861, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                            · linarith only [h2852, h2861, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                          · linarith only [h2657, h2852, h2860, hlam]
                        · linarith only [h2657, h2851, h2852, h2858, h2859, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi4]
                      · linarith only [h1989, h2850, h2858, hlam]
                    · linarith only [h2657, h2852, h2854, h2857, hlam]
                  · linarith only [h1989, h2850, h2853, h2856, hlam]
                · linarith only [h1989, h2850, h2853, h2855, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h1989, h2850, h2852, h2853, h2854, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2871 | h2871
              · linarith only [h0, h2657, h2853, h2871, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2873 | h2873
                · linarith only [h0, h2768, h2853, h2873, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2875 | h2875
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2876 | h2876
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2877 | h2877
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2878 | h2878
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2879 | h2879
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2880 | h2880
                            · linarith only [h2850, h2880, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                            · linarith only [h2852, h2880, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                          · linarith only [h2850, h2852, h2879, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
                        · linarith only [h0, h1989, h2851, h2878, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1180, h2850, h2853, h2877, hlam]
                    · linarith only [h1692, h2852, h2876, hlam]
                  · linarith only [h1180, h2850, h2875, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2888 | h2888
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2889 | h2889
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2890 | h2890
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2891 | h2891
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2892 | h2892
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2893 | h2893
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2894 | h2894
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2895 | h2895
                          · linarith only [h2850, h2852, h2889, h2895, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h0, h2657, h2892, h2895, hc01, hc14, hlam, hphi]
                        · linarith only [h0, h1989, h2851, h2894, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1989, h2850, h2851, h2852, h2891, h2892, h2893, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2900 | h2900
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2901 | h2901
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2902 | h2902
                          · linarith only [h2889, h2892, h2902, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2904 | h2904
                            · linarith only [h1692, h2892, h2904, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c | h2906c
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [hlam, p2906_0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h0, hlam, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h1180, hlam, p2906_0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h1692, hlam, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h1845, hlam, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h2657, h2889, hc01, hc14, hlam, hphi, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [hlam, p2906_0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h1989, hlam, p2906_0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h2657, hlam, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h2768, hlam, p2906_0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h1989, h2888, hc01, hc12, hlam, hphi, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h0, h1989, h2888, hc01, hc12, hlam, hphi, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [hlam, p2906_0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h1989, h2888, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2906_1, u4ehi0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h1845, h1989, h2888, hc01, hc12, hlam, hphi, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h1692, h2892, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h0, h2657, h2889, h2892, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h2850, hlam, p2906_0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [hlam, p2906_0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h2852, hlam, p2906_0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h1989, h2851, h2888, hc01, hc12, hlam, hphi, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h0, h1989, h2851, h2888, hc01, hc12, hlam, hphi, p2906_1]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h2851, hlam, p2906_0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [h1989, h2851, h2888, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2906_1, u4ehi0]
                              · have p2906_0 := h2906c.1
                                have p2906_1 := h2906c.2.1
                                have p2906_2 := h2906c.2.2.1
                                have p2906_3 := h2906c.2.2.2
                                linarith only [hlam, p2906_0]
                        · linarith only [h1989, h2851, h2901, hlam]
                      · linarith only [h0, h1692, h1989, h2850, h2892, h2900, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h1180, h2850, h2891, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h1989, h2850, h2888, h2890, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h1989, h2850, h2888, h2889, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2937 | h2937
              · linarith only [h0, h2657, h2888, h2937, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2939 | h2939
                · linarith only [h0, h2768, h2888, h2939, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2941 | h2941
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2942 | h2942
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2943 | h2943
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2944 | h2944
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2945 | h2945
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2946 | h2946
                            · linarith only [h2850, h2852, h2946, hlam]
                            · rcases h0bigk with h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c | h2948c
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [hlam, p2948_0]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h0, hlam, p2948_1]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h1180, hlam, p2948_0]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h1692, hlam, p2948_1]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h1845, hlam, p2948_1]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h0, h2939, h2943, h2945, hc01, hc23, hlam, hphi, ht12, p2948_1]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [hlam, p2948_0]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h1989, hlam, p2948_0]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h2657, hlam, p2948_1]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h2768, hlam, p2948_0]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                rcases p2948_3 (m.d 0 1) (by simp) with h2959 | h2959
                                · linarith only [h1180, h2959, hlam]
                                · rcases p2948_3 (m.d 0 2) (by simp) with h2961 | h2961
                                  · linarith only [h1989, h2961, hlam]
                                  · linarith only [h0, h2961, hlam]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                rcases p2948_3 (m.d 0 1) (by simp) with h2964 | h2964
                                · linarith only [h1180, h2964, hlam]
                                · rcases p2948_3 (m.d 0 2) (by simp) with h2966 | h2966
                                  · linarith only [h1989, h2966, hlam]
                                  · rcases p2948_3 (m.d 0 3) (by simp) with h2968 | h2968
                                    · rcases p2948_3 (m.d 0 4) (by simp) with h2969 | h2969
                                      · linarith only [h2850, h2969, hlam]
                                      · linarith only [h2657, h2969, hlam]
                                    · linarith only [h1989, h2968, hlam]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [hlam, p2948_0]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h2850, hlam, hphi, ht0b, ht45, ht5b, p2948_1, u0elo2, u4ehi3]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h2850, h2852, hlam, hphi, ht0b, ht45, ht5b, p2948_1, u0elo2, u4ehi3]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h2852, h2941, h2942, hc01, hc13, hlam, hphi, p2948_1]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h0, h2852, h2941, h2942, hc01, hc13, hlam, hphi, p2948_1]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h2850, hlam, p2948_0]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [hlam, p2948_0]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h2852, hlam, p2948_0]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h2852, h2941, h2942, hc01, hc13, hlam, hphi, p2948_1]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h0, h2852, h2941, h2942, hc01, hc13, hlam, hphi, p2948_1]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h2851, hlam, p2948_0]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [h2852, h2941, h2942, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p2948_1, u4ehi0]
                              · have p2948_0 := h2948c.1
                                have p2948_1 := h2948c.2.1
                                have p2948_2 := h2948c.2.2.1
                                have p2948_3 := h2948c.2.2.2
                                linarith only [hlam, p2948_0]
                          · linarith only [h0, h2657, h2888, h2941, h2942, h2945, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h1180, h2851, h2888, h2944, hlam]
                      · linarith only [h2850, h2852, h2888, h2941, h2942, h2943, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2989 | h2989
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2990 | h2990
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2991 | h2991
                          · linarith only [h0, h2937, h2942, h2991, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h2937, h2991, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h1180, h2851, h2888, h2990, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1180, h2850, h2888, h2989, hlam]
                  · linarith only [h1180, h2850, h2941, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2997 | h2997
          · linarith only [h2850, h2851, h2997, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2999 | h2999
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3000 | h3000
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3001 | h3001
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3002 | h3002
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3003 | h3003
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3004 | h3004
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3005 | h3005
                        · linarith only [h2850, h2851, h3005, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3007 | h3007
                          · linarith only [h2997, h3000, h3007, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h2657, h2999, h3002, h3003, h3007, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h1989, h2850, h3004, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3011 | h3011
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3012 | h3012
                        · linarith only [h2850, h2851, h3012, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3014 | h3014
                          · linarith only [h1692, h3003, h3014, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3016 | h3016
                            · linarith only [h0, h2657, h2850, h3000, h3003, h3016, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1989, h2850, h3012, h3016, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h1989, h2850, h3011, hlam]
                  · linarith only [h1180, h2850, h3002, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h1989, h2850, h2999, h3001, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h1989, h2850, h2999, h3000, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3023 | h3023
              · linarith only [h0, h2657, h2999, h3023, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3025 | h3025
                · linarith only [h0, h2768, h2999, h3025, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3027 | h3027
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3028 | h3028
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3029 | h3029
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3030 | h3030
                        · linarith only [h2850, h2851, h3030, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h3023, h3029, h3030, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h2850, h2851, h2997, h2999, h3027, h3028, h3029, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3034 | h3034
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3035 | h3035
                        · linarith only [h2850, h2851, h3035, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h2999, h3035, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h2850, h2999, h3034, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h2850, h2851, h3027, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3040 | h3040
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3041 | h3041
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3042 | h3042
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3043 | h3043
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3044 | h3044
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3045 | h3045
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3046 | h3046
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3047 | h3047
                      · linarith only [h2850, h3040, h3042, h3047, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h1989, h3042, h3045, h3047, hc01, hc12, hlam, hphi]
                    · linarith only [h3041, h3046, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3051 | h3051
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3052 | h3052
                      · linarith only [h2850, h3040, h3041, h3042, h3052, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3054 | h3054
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3055 | h3055
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3056 | h3056
                            · rcases h0bigk with h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c | h3057c
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [hlam, p3057_0]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h0, hlam, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h1180, hlam, p3057_0]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h1692, hlam, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h1845, hlam, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h2768, h3044, hc01, hc15, hlam, hphi, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [hlam, p3057_0]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h1989, hlam, p3057_0]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h2657, hlam, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h2768, hlam, p3057_0]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h1989, h3042, h3045, hc01, hc34, hlam, hphi, ht12, ht23, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h1989, h3042, h3045, hc02, hc34, hlam, hphi, ht23, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [hlam, p3057_0]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h2850, hlam, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h1989, h3040, h3042, h3045, h3056, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3057_1, u4ehi4]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h2657, h3043, hc01, hc12, hlam, hphi, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h0, h2657, h3043, hc01, hc12, hlam, hphi, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h3040, h3056, hlam, hphi, ht0b, ht45, ht5b, p3057_1, u0elo3, u4ehi4]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [hlam, p3057_0]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h3040, h3056, hlam, hphi, ht0b, ht45, ht5b, p3057_1, u0elo3, u4ehi4]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h1989, h3040, h3042, h3045, hc01, hc34, hlam, hphi, ht12, ht23, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h1989, h3040, h3042, h3045, hc02, hc34, hlam, hphi, ht23, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h3040, hlam, p3057_0]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [h3041, hlam, p3057_1]
                              · have p3057_0 := h3057c.1
                                have p3057_1 := h3057c.2.1
                                have p3057_2 := h3057c.2.2.1
                                have p3057_3 := h3057c.2.2.2
                                linarith only [hlam, p3057_0]
                            · linarith only [h1180, h3045, h3056, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h2657, h3041, h3055, hlam]
                        · linarith only [h1989, h3040, h3054, hlam]
                    · linarith only [h2657, h3041, h3043, h3051, hlam]
                · linarith only [h2657, h3041, h3043, h3044, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h0, h1989, h3042, h3043, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3089 | h3089
              · linarith only [h0, h2657, h3042, h3089, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3091 | h3091
                · linarith only [h0, h2768, h3042, h3091, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3093 | h3093
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3094 | h3094
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3095 | h3095
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3096 | h3096
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3097 | h3097
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3098 | h3098
                            · linarith only [h2850, h3040, h3093, h3098, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h2850, h3041, h3098, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h2850, h3040, h3041, h3042, h3093, h3097, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h2850, h3042, h3093, h3096, hc03, hc35, hlam, hphi]
                      · linarith only [h3042, h3093, h3095, hlam]
                    · linarith only [h2850, h3040, h3041, h3093, h3094, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3105 | h3105
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3106 | h3106
                      · linarith only [h1180, h3093, h3106, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h3042, h3106, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1692, h2850, h3040, h3041, h3105, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h2850, h3040, h3041, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3111 | h3111
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3112 | h3112
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3113 | h3113
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3114 | h3114
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3115 | h3115
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3116 | h3116
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3117 | h3117
                      · linarith only [h2850, h3111, h3112, h3117, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h1989, h3115, h3117, hc01, hc13, hlam, hphi]
                    · linarith only [h2657, h3111, h3113, h3116, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3121 | h3121
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3122 | h3122
                      · linarith only [h1180, h3115, h3122, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3124 | h3124
                        · linarith only [h3040, h3112, h3115, h3124, hc03, hc34, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3126 | h3126
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3127 | h3127
                            · rcases h0bigk with h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c | h3128c
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [hlam, p3128_0]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h0, hlam, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h1180, hlam, p3128_0]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h1692, hlam, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h1845, hlam, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h1180, h1989, h3115, hc01, hc34, hlam, hphi, ht12, ht23, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [hlam, p3128_0]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h1989, hlam, p3128_0]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h2657, hlam, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h2768, hlam, p3128_0]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h1180, h3115, hc01, hc34, hlam, hphi, ht12, ht23, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h1180, h3115, hc02, hc34, hlam, hphi, ht23, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [hlam, p3128_0]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h2850, hlam, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h3040, hlam, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h2657, h3113, hc01, hc12, hlam, hphi, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h0, h2657, h3113, hc01, hc12, hlam, hphi, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h0, h1989, h2657, h3113, hc01, hc12, hlam, hphi, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [hlam, p3128_0]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h3111, hlam, hphi, ht0b, ht45, ht5b, p3128_1, u0elo3, u4ehi4]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h2657, h3111, h3113, hc01, hc12, hlam, hphi, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h0, h2657, h3111, h3113, hc01, hc12, hlam, hphi, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h0, h1989, h2657, h3111, h3113, hc01, hc12, hlam, hphi, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [h3111, hlam, p3128_1]
                              · have p3128_0 := h3128c.1
                                have p3128_1 := h3128c.2.1
                                have p3128_2 := h3128c.2.2.1
                                have p3128_3 := h3128c.2.2.2
                                linarith only [hlam, p3128_0]
                            · linarith only [h1180, h3115, h3127, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h2657, h3111, h3126, hlam]
                    · linarith only [h2657, h3111, h3113, h3121, hlam]
                · linarith only [h2657, h3111, h3113, h3114, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h0, h1989, h3112, h3113, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3159 | h3159
              · linarith only [h2657, h3111, h3112, h3159, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3161 | h3161
                · linarith only [h0, h2768, h3112, h3161, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3163 | h3163
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3164 | h3164
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3165 | h3165
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3166 | h3166
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3167 | h3167
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3168 | h3168
                            · rcases h0bigk with h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c | h3169c
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [hlam, p3169_0]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h0, hlam, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h1180, hlam, p3169_0]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h1692, hlam, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h1845, hlam, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h0, h3161, h3165, h3167, hc01, hc23, hlam, hphi, ht12, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [hlam, p3169_0]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h1989, hlam, p3169_0]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h2657, hlam, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h2768, hlam, p3169_0]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h2850, h3163, hc01, hc13, hlam, hphi, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h2850, h3163, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [hlam, p3169_0]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h2850, hlam, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h3040, hlam, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h2850, h3163, hc01, hc13, hlam, hphi, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h0, h2850, h3163, hc01, hc13, hlam, hphi, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h1180, h2850, h3163, hc01, hc13, hlam, hphi, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [hlam, p3169_0]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h1845, h2850, h3163, hc01, hc13, hlam, hphi, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h3040, h3163, h3168, hc01, hc13, hlam, hphi, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h0, h3040, h3163, h3168, hc01, hc13, hlam, hphi, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h0, h1989, h3040, h3163, h3168, hc01, hc13, hlam, hphi, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [h3111, hlam, p3169_1]
                              · have p3169_0 := h3169c.1
                                have p3169_1 := h3169c.2.1
                                have p3169_2 := h3169c.2.2.1
                                have p3169_3 := h3169c.2.2.2
                                linarith only [hlam, p3169_0]
                            · linarith only [h2850, h3111, h3168, hlam]
                          · linarith only [h2850, h3111, h3112, h3163, h3167, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h2850, h3111, h3112, h3163, h3166, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h3112, h3163, h3165, hlam]
                    · linarith only [h2850, h3111, h3163, h3164, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3200 | h3200
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3201 | h3201
                      · linarith only [h1180, h3163, h3201, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h3112, h3201, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h3111, h3200, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3205 | h3205
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3206 | h3206
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3207 | h3207
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3208 | h3208
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3209 | h3209
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3210 | h3210
                      · linarith only [h0, h1989, h2850, h3205, h3210, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h1989, h3205, h3208, h3210, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3213 | h3213
                      · linarith only [h0, h1989, h2850, h3205, h3213, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h1989, h3208, h3209, h3213, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3216 | h3216
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3217 | h3217
                      · linarith only [h1180, h3208, h3217, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3219 | h3219
                        · linarith only [h0, h1989, h3040, h3205, h3219, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3221 | h3221
                          · linarith only [h3111, h3206, h3221, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h2657, h3208, h3216, h3221, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3224 | h3224
                      · linarith only [h3205, h3208, h3216, h3224, hc45, hlam, hphi, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3226 | h3226
                        · linarith only [h0, h1989, h3040, h3205, h3208, h3216, h3226, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3228 | h3228
                          · linarith only [h1180, h3208, h3216, h3228, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3230 | h3230
                            · linarith only [h0, h1989, h3205, h3208, h3216, h3230, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h1989, h3205, h3208, h3230, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h1989, h3205, h3207, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h1989, h3205, h3206, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3235 | h3235
              · linarith only [h0, h2657, h3205, h3235, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3237 | h3237
                · linarith only [h0, h2768, h3205, h3237, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3239 | h3239
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3240 | h3240
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3241 | h3241
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3242 | h3242
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3243 | h3243
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3244 | h3244
                            · linarith only [h3111, h3205, h3239, h3244, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · linarith only [h0, h1989, h2850, h3205, h3239, h3240, h3244, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h2657, h3205, h3239, h3240, h3243, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h3111, h3205, h3239, h3240, h3242, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                      · linarith only [h3111, h3205, h3239, h3240, h3241, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3250 | h3250
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3251 | h3251
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3252 | h3252
                          · linarith only [h1692, h3240, h3252, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h3235, h3252, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h3205, h3251, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h3205, h3239, h3250, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3257 | h3257
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3258 | h3258
                      · linarith only [h3111, h3239, h3257, h3258, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · linarith only [h0, h3205, h3258, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3261 | h3261
                      · linarith only [h1180, h3239, h3261, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h3205, h3261, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1180 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1692 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1845 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1989 | h1989
  · exact r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x1_x1_x0 m hb0 hb2 hb4 h0 h1180 h1692 h1845 h1989
  · exact r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x1_x1_x1 m hb0 hb2 hb4 h0 h1180 h1692 h1845 h1989

set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1180 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1692 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1845 | h1845
  · exact r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x1_x0 m hb0 hb2 hb4 h0 h1180 h1692 h1845
  · exact r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x1_x1 m hb0 hb2 hb4 h0 h1180 h1692 h1845

set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_R_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1180 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1692 | h1692
  · exact r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x0 m hb0 hb2 hb4 h0 h1180 h1692
  · exact r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x1 m hb0 hb2 hb4 h0 h1180 h1692

set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1180 | h1180
  · exact r1l7_20_12_14_M_LI_L_I_L_R_x1_x0 m hb0 hb2 hb4 h0 h1180
  · exact r1l7_20_12_14_M_LI_L_I_L_R_x1_x1 m hb0 hb2 hb4 h0 h1180

set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_M_LI_L_I_L_R_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_M_LI_L_I_L_R_x1 m hb0 hb2 hb4 h0

end R2N4
