import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S3
import Jsp000404.R1LeavesN7_8S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2063 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h2142 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h2674 | h2674
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2675 | h2675
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2676 | h2676
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2677 | h2677
        · linarith only [h1, h2677, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2679 | h2679
          · linarith only [h1, h2063, h2679, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2681 | h2681
            · linarith only [h2, h2142, h2681, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2683 | h2683
              · linarith only [h1, h2674, h2683, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2685 | h2685
                · linarith only [h1, h2063, h2674, h2685, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2687 | h2687
                  · linarith only [h0, h2142, h2675, h2687, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2689 | h2689
                    · rcases h0bigk with h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c | h2690c
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [hlam, p2690_0]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h0, h2676, hc01, hlam, hphi, ht0b, ht5b, p2690_1, u5ehi2]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        rcases p2690_3 (m.d 0 1) (by simp) with h2693 | h2693
                        · rcases p2690_3 (m.d 0 2) (by simp) with h2694 | h2694
                          · linarith only [h0, h2694, hlam]
                          · linarith only [h2694, h4, hlam]
                        · linarith only [h1, h2693, hlam]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        rcases p2690_3 (m.d 0 1) (by simp) with h2698 | h2698
                        · rcases p2690_3 (m.d 0 2) (by simp) with h2699 | h2699
                          · linarith only [h0, h2699, hlam]
                          · linarith only [h2699, h5, hlam]
                        · linarith only [h2, h2698, hlam]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        rcases p2690_3 (m.d 0 1) (by simp) with h2703 | h2703
                        · rcases p2690_3 (m.d 0 2) (by simp) with h2704 | h2704
                          · linarith only [h0, h2704, hlam]
                          · linarith only [h2704, h6, hlam]
                        · linarith only [h2703, h3, hlam]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h0, hlam, p2690_0]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [hlam, p2690_0]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        rcases p2690_3 (m.d 0 1) (by simp) with h2710 | h2710
                        · rcases p2690_3 (m.d 0 2) (by simp) with h2711 | h2711
                          · rcases p2690_3 (m.d 0 3) (by simp) with h2712 | h2712
                            · linarith only [h2712, h4, hlam]
                            · rcases p2690_3 (m.d 0 4) (by simp) with h2714 | h2714
                              · linarith only [h2714, h5, hlam]
                              · linarith only [h2714, h7, hlam]
                          · linarith only [h2711, h4, hlam]
                        · linarith only [h1, h2710, hlam]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        rcases p2690_3 (m.d 0 1) (by simp) with h2719 | h2719
                        · rcases p2690_3 (m.d 0 2) (by simp) with h2720 | h2720
                          · rcases p2690_3 (m.d 0 3) (by simp) with h2721 | h2721
                            · linarith only [h2721, h4, hlam]
                            · rcases p2690_3 (m.d 0 4) (by simp) with h2723 | h2723
                              · linarith only [h2723, h5, hlam]
                              · rcases p2690_3 (m.d 0 5) (by simp) with h2725 | h2725
                                · linarith only [h2725, h6, hlam]
                                · linarith only [h2142, h2725, hlam]
                          · linarith only [h2720, h5, hlam]
                        · linarith only [h2, h2719, hlam]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        rcases p2690_3 (m.d 0 1) (by simp) with h2730 | h2730
                        · rcases p2690_3 (m.d 0 2) (by simp) with h2731 | h2731
                          · rcases p2690_3 (m.d 0 3) (by simp) with h2732 | h2732
                            · linarith only [h2732, h4, hlam]
                            · rcases p2690_3 (m.d 0 4) (by simp) with h2734 | h2734
                              · linarith only [h2734, h5, hlam]
                              · rcases p2690_3 (m.d 0 5) (by simp) with h2736 | h2736
                                · linarith only [h2736, h6, hlam]
                                · rcases h2bigk with h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h0, h2676, hc01, hlam, hphi, ht0b, ht5b, p2738_1, u5ehi2]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    rcases p2738_3 (m.d 0 2) (by simp) with h2741 | h2741
                                    · rcases p2738_3 (m.d 1 2) (by simp) with h2742 | h2742
                                      · linarith only [h0, h2742, hlam]
                                      · linarith only [h2674, h2742, hlam]
                                    · linarith only [h2741, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    rcases p2738_3 (m.d 0 2) (by simp) with h2746 | h2746
                                    · rcases p2738_3 (m.d 1 2) (by simp) with h2747 | h2747
                                      · linarith only [h0, h2747, hlam]
                                      · linarith only [h2675, h2747, hlam]
                                    · linarith only [h2746, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    rcases p2738_3 (m.d 0 2) (by simp) with h2751 | h2751
                                    · rcases p2738_3 (m.d 1 2) (by simp) with h2752 | h2752
                                      · linarith only [h0, h2752, hlam]
                                      · linarith only [h2676, h2752, hlam]
                                    · linarith only [h2751, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h0, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    rcases p2738_3 (m.d 0 2) (by simp) with h2758 | h2758
                                    · rcases p2738_3 (m.d 1 2) (by simp) with h2759 | h2759
                                      · rcases p2738_3 (m.d 2 3) (by simp) with h2760 | h2760
                                        · linarith only [h2760, hlam, p2738_0]
                                        · rcases p2738_3 (m.d 2 4) (by simp) with h2762 | h2762
                                          · linarith only [h2675, h2762, hlam]
                                          · linarith only [h2683, h2762, hlam]
                                      · linarith only [h2759, hlam, p2738_0]
                                    · linarith only [h2758, h4, hlam]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    rcases p2738_3 (m.d 0 2) (by simp) with h2767 | h2767
                                    · rcases p2738_3 (m.d 1 2) (by simp) with h2768 | h2768
                                      · rcases p2738_3 (m.d 2 3) (by simp) with h2769 | h2769
                                        · linarith only [h2674, h2769, hlam]
                                        · rcases p2738_3 (m.d 2 4) (by simp) with h2771 | h2771
                                          · linarith only [h2771, hlam, p2738_0]
                                          · rcases p2738_3 (m.d 2 5) (by simp) with h2773 | h2773
                                            · linarith only [h2676, h2773, hlam]
                                            · linarith only [h2687, h2773, hlam]
                                      · linarith only [h2768, hlam, p2738_0]
                                    · linarith only [h2767, h5, hlam]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p2738_1, u5ehi2]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h4, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h2674, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h2683, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h2685, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h5, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h2675, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h2, h2142, h2675, h2689, hc23, hc34, hlam, hphi, p2738_1]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h2687, hlam, p2738_1]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h6, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h2676, hlam, p2738_0]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h6, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2690_1, p2738_1]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [h0, h2676, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2690_1, p2738_1]
                                  · have p2738_0 := h2738c.1
                                    have p2738_1 := h2738c.2.1
                                    have p2738_2 := h2738c.2.2.1
                                    have p2738_3 := h2738c.2.2.2
                                    linarith only [hlam, p2738_0]
                          · linarith only [h2731, h6, hlam]
                        · linarith only [h2730, h3, hlam]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h1, hlam, p2690_1]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h4, hlam, p2690_1]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [hlam, p2690_0]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h7, hlam, p2690_1]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h2063, hlam, p2690_1]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h2, hlam, p2690_0]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h5, hlam, p2690_0]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h1, h2142, h2674, h2689, hc23, hc34, hlam, hphi, p2690_1]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [hlam, p2690_0]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h2142, hlam, p2690_0]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h3, hlam, p2690_0]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h6, hlam, p2690_1]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h1, h2142, h2674, h2689, hc23, hc34, hlam, hphi, p2690_1]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [h1, h2142, h2674, h2689, h7, hc23, hc34, hlam, hphi, p2690_1]
                      · have p2690_0 := h2690c.1
                        have p2690_1 := h2690c.2.1
                        have p2690_2 := h2690c.2.2.1
                        have p2690_3 := h2690c.2.2.2
                        linarith only [hlam, p2690_0]
                    · rcases h0bigk with h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c | h2811c
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [hlam, p2811_0]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h0, h2676, hc01, hlam, hphi, ht0b, ht5b, p2811_1, u5ehi2]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        rcases p2811_3 (m.d 0 1) (by simp) with h2814 | h2814
                        · rcases p2811_3 (m.d 0 2) (by simp) with h2815 | h2815
                          · linarith only [h0, h2815, hlam]
                          · linarith only [h2815, h4, hlam]
                        · linarith only [h1, h2814, hlam]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        rcases p2811_3 (m.d 0 1) (by simp) with h2819 | h2819
                        · rcases p2811_3 (m.d 0 2) (by simp) with h2820 | h2820
                          · linarith only [h0, h2820, hlam]
                          · linarith only [h2820, h5, hlam]
                        · linarith only [h2, h2819, hlam]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        rcases p2811_3 (m.d 0 1) (by simp) with h2824 | h2824
                        · rcases p2811_3 (m.d 0 2) (by simp) with h2825 | h2825
                          · linarith only [h0, h2825, hlam]
                          · linarith only [h2825, h6, hlam]
                        · linarith only [h2824, h3, hlam]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h0, hlam, p2811_0]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [hlam, p2811_0]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        rcases p2811_3 (m.d 0 1) (by simp) with h2831 | h2831
                        · rcases p2811_3 (m.d 0 2) (by simp) with h2832 | h2832
                          · rcases p2811_3 (m.d 0 3) (by simp) with h2833 | h2833
                            · linarith only [h2833, h4, hlam]
                            · rcases p2811_3 (m.d 0 4) (by simp) with h2835 | h2835
                              · linarith only [h2835, h5, hlam]
                              · linarith only [h2835, h7, hlam]
                          · linarith only [h2832, h4, hlam]
                        · linarith only [h1, h2831, hlam]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        rcases p2811_3 (m.d 0 1) (by simp) with h2840 | h2840
                        · rcases p2811_3 (m.d 0 2) (by simp) with h2841 | h2841
                          · rcases p2811_3 (m.d 0 3) (by simp) with h2842 | h2842
                            · linarith only [h2842, h4, hlam]
                            · rcases p2811_3 (m.d 0 4) (by simp) with h2844 | h2844
                              · linarith only [h2844, h5, hlam]
                              · rcases p2811_3 (m.d 0 5) (by simp) with h2846 | h2846
                                · linarith only [h2846, h6, hlam]
                                · linarith only [h2142, h2846, hlam]
                          · linarith only [h2841, h5, hlam]
                        · linarith only [h2, h2840, hlam]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        rcases p2811_3 (m.d 0 1) (by simp) with h2851 | h2851
                        · rcases p2811_3 (m.d 0 2) (by simp) with h2852 | h2852
                          · rcases p2811_3 (m.d 0 3) (by simp) with h2853 | h2853
                            · linarith only [h2853, h4, hlam]
                            · rcases p2811_3 (m.d 0 4) (by simp) with h2855 | h2855
                              · linarith only [h2855, h5, hlam]
                              · rcases p2811_3 (m.d 0 5) (by simp) with h2857 | h2857
                                · linarith only [h2857, h6, hlam]
                                · rcases h2bigk with h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c | h2859c
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h0, h2676, hc01, hlam, hphi, ht0b, ht5b, p2859_1, u5ehi2]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    rcases p2859_3 (m.d 0 2) (by simp) with h2862 | h2862
                                    · rcases p2859_3 (m.d 1 2) (by simp) with h2863 | h2863
                                      · linarith only [h0, h2863, hlam]
                                      · linarith only [h2674, h2863, hlam]
                                    · linarith only [h2862, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    rcases p2859_3 (m.d 0 2) (by simp) with h2867 | h2867
                                    · rcases p2859_3 (m.d 1 2) (by simp) with h2868 | h2868
                                      · linarith only [h0, h2868, hlam]
                                      · linarith only [h2675, h2868, hlam]
                                    · linarith only [h2867, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    rcases p2859_3 (m.d 0 2) (by simp) with h2872 | h2872
                                    · rcases p2859_3 (m.d 1 2) (by simp) with h2873 | h2873
                                      · linarith only [h0, h2873, hlam]
                                      · linarith only [h2676, h2873, hlam]
                                    · linarith only [h2872, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h0, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    rcases p2859_3 (m.d 0 2) (by simp) with h2879 | h2879
                                    · rcases p2859_3 (m.d 1 2) (by simp) with h2880 | h2880
                                      · rcases p2859_3 (m.d 2 3) (by simp) with h2881 | h2881
                                        · linarith only [h2881, hlam, p2859_0]
                                        · rcases p2859_3 (m.d 2 4) (by simp) with h2883 | h2883
                                          · linarith only [h2675, h2883, hlam]
                                          · linarith only [h2683, h2883, hlam]
                                      · linarith only [h2880, hlam, p2859_0]
                                    · linarith only [h2879, h4, hlam]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    rcases p2859_3 (m.d 0 2) (by simp) with h2888 | h2888
                                    · rcases p2859_3 (m.d 1 2) (by simp) with h2889 | h2889
                                      · rcases p2859_3 (m.d 2 3) (by simp) with h2890 | h2890
                                        · linarith only [h2674, h2890, hlam]
                                        · rcases p2859_3 (m.d 2 4) (by simp) with h2892 | h2892
                                          · linarith only [h2892, hlam, p2859_0]
                                          · rcases p2859_3 (m.d 2 5) (by simp) with h2894 | h2894
                                            · linarith only [h2676, h2894, hlam]
                                            · linarith only [h2687, h2894, hlam]
                                      · linarith only [h2889, hlam, p2859_0]
                                    · linarith only [h2888, h5, hlam]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p2859_1, u5ehi2]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h4, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h2674, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h2683, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h2685, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h5, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h2675, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h2689, h5, h7, hc23, hc45, hlam, hphi, ht34, p2859_1]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h2687, hlam, p2859_1]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h6, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h2676, hlam, p2859_0]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h2676, h3, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2811_1, p2859_1]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [h0, h2676, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2811_1, p2859_1]
                                  · have p2859_0 := h2859c.1
                                    have p2859_1 := h2859c.2.1
                                    have p2859_2 := h2859c.2.2.1
                                    have p2859_3 := h2859c.2.2.2
                                    linarith only [hlam, p2859_0]
                          · linarith only [h2852, h6, hlam]
                        · linarith only [h2851, h3, hlam]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h1, hlam, p2811_1]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h4, hlam, p2811_1]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [hlam, p2811_0]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h7, hlam, p2811_1]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h2063, hlam, p2811_1]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h2, hlam, p2811_0]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h5, hlam, p2811_0]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h1, h2674, h2689, h7, hc23, hc45, hlam, hphi, ht34, p2811_1]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [hlam, p2811_0]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h2142, hlam, p2811_0]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h3, hlam, p2811_0]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [h6, hlam, p2811_1]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        rcases p2811_3 (m.d 0 1) (by simp) with h2929 | h2929
                        · rcases p2811_3 (m.d 0 2) (by simp) with h2930 | h2930
                          · rcases p2811_3 (m.d 0 3) (by simp) with h2931 | h2931
                            · linarith only [h2063, h2931, hlam]
                            · rcases p2811_3 (m.d 0 4) (by simp) with h2933 | h2933
                              · linarith only [h2142, h2933, hlam]
                              · linarith only [h2933, h7, hlam]
                          · linarith only [h2930, h4, hlam]
                        · linarith only [h1, h2929, hlam]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        rcases p2811_3 (m.d 0 1) (by simp) with h2938 | h2938
                        · rcases p2811_3 (m.d 0 2) (by simp) with h2939 | h2939
                          · rcases p2811_3 (m.d 0 3) (by simp) with h2940 | h2940
                            · linarith only [h2063, h2940, hlam]
                            · rcases p2811_3 (m.d 0 4) (by simp) with h2942 | h2942
                              · linarith only [h2142, h2942, hlam]
                              · rcases p2811_3 (m.d 0 5) (by simp) with h2944 | h2944
                                · rcases h2bigk with h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h0, h2676, hc01, hlam, hphi, ht0b, ht5b, p2945_1, u5ehi2]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    rcases p2945_3 (m.d 0 2) (by simp) with h2948 | h2948
                                    · rcases p2945_3 (m.d 1 2) (by simp) with h2949 | h2949
                                      · linarith only [h0, h2949, hlam]
                                      · linarith only [h2674, h2949, hlam]
                                    · linarith only [h2948, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    rcases p2945_3 (m.d 0 2) (by simp) with h2953 | h2953
                                    · rcases p2945_3 (m.d 1 2) (by simp) with h2954 | h2954
                                      · linarith only [h0, h2954, hlam]
                                      · linarith only [h2675, h2954, hlam]
                                    · linarith only [h2953, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    rcases p2945_3 (m.d 0 2) (by simp) with h2958 | h2958
                                    · rcases p2945_3 (m.d 1 2) (by simp) with h2959 | h2959
                                      · linarith only [h0, h2959, hlam]
                                      · linarith only [h2676, h2959, hlam]
                                    · linarith only [h2958, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h0, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    rcases p2945_3 (m.d 0 2) (by simp) with h2965 | h2965
                                    · rcases p2945_3 (m.d 1 2) (by simp) with h2966 | h2966
                                      · rcases p2945_3 (m.d 2 3) (by simp) with h2967 | h2967
                                        · linarith only [h2967, hlam, p2945_0]
                                        · rcases p2945_3 (m.d 2 4) (by simp) with h2969 | h2969
                                          · linarith only [h2675, h2969, hlam]
                                          · linarith only [h2683, h2969, hlam]
                                      · linarith only [h2966, hlam, p2945_0]
                                    · linarith only [h2965, h4, hlam]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    rcases p2945_3 (m.d 0 2) (by simp) with h2974 | h2974
                                    · rcases p2945_3 (m.d 1 2) (by simp) with h2975 | h2975
                                      · rcases p2945_3 (m.d 2 3) (by simp) with h2976 | h2976
                                        · linarith only [h2674, h2976, hlam]
                                        · rcases p2945_3 (m.d 2 4) (by simp) with h2978 | h2978
                                          · linarith only [h2978, hlam, p2945_0]
                                          · rcases p2945_3 (m.d 2 5) (by simp) with h2980 | h2980
                                            · linarith only [h2676, h2980, hlam]
                                            · linarith only [h2687, h2980, hlam]
                                      · linarith only [h2975, hlam, p2945_0]
                                    · linarith only [h2974, h5, hlam]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p2945_1, u5ehi2]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h4, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h2674, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h2683, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h2685, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h5, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h2675, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h5, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2811_1, p2945_1]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h2687, hlam, p2945_1]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h6, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h2676, hlam, p2945_0]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h0, h2676, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2945_1]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [h0, h2676, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2945_1]
                                  · have p2945_0 := h2945c.1
                                    have p2945_1 := h2945c.2.1
                                    have p2945_2 := h2945c.2.2.1
                                    have p2945_3 := h2945c.2.2.2
                                    linarith only [hlam, p2945_0]
                                · linarith only [h2142, h2944, hlam]
                          · linarith only [h2939, h5, hlam]
                        · linarith only [h2, h2938, hlam]
                      · have p2811_0 := h2811c.1
                        have p2811_1 := h2811c.2.1
                        have p2811_2 := h2811c.2.2.1
                        have p2811_3 := h2811c.2.2.2
                        linarith only [hlam, p2811_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3005 | h3005
        · linarith only [h1, h3005, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3007 | h3007
          · linarith only [h1, h2063, h3007, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3009 | h3009
            · linarith only [h2142, h2675, h2676, h3009, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3011 | h3011
              · linarith only [h3011, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3013 | h3013
                · linarith only [h1, h2063, h2674, h2676, h3013, h6, h7, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3015 | h3015
                  · linarith only [h0, h2142, h2675, h2676, h3015, h6, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3017 | h3017
                    · linarith only [h2142, h2675, h2676, h3011, h3017, h6, hc23, hc34, hlam, hphi]
                    · rcases h0bigk with h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [hlam, p3019_0]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h2675, h2676, h3011, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3019_1]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        rcases p3019_3 (m.d 0 1) (by simp) with h3022 | h3022
                        · rcases p3019_3 (m.d 0 2) (by simp) with h3023 | h3023
                          · linarith only [h0, h3023, hlam]
                          · linarith only [h3023, h4, hlam]
                        · linarith only [h1, h3022, hlam]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        rcases p3019_3 (m.d 0 1) (by simp) with h3027 | h3027
                        · rcases p3019_3 (m.d 0 2) (by simp) with h3028 | h3028
                          · linarith only [h0, h3028, hlam]
                          · linarith only [h3028, h5, hlam]
                        · linarith only [h2, h3027, hlam]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h2675, h2676, h3011, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3019_1]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h0, hlam, p3019_0]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [hlam, p3019_0]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        rcases p3019_3 (m.d 0 1) (by simp) with h3035 | h3035
                        · rcases p3019_3 (m.d 0 2) (by simp) with h3036 | h3036
                          · rcases p3019_3 (m.d 0 3) (by simp) with h3037 | h3037
                            · linarith only [h3037, h4, hlam]
                            · rcases p3019_3 (m.d 0 4) (by simp) with h3039 | h3039
                              · linarith only [h3039, h5, hlam]
                              · linarith only [h3039, h7, hlam]
                          · linarith only [h3036, h4, hlam]
                        · linarith only [h1, h3035, hlam]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        rcases p3019_3 (m.d 0 1) (by simp) with h3044 | h3044
                        · rcases p3019_3 (m.d 0 2) (by simp) with h3045 | h3045
                          · rcases p3019_3 (m.d 0 3) (by simp) with h3046 | h3046
                            · linarith only [h3046, h4, hlam]
                            · rcases p3019_3 (m.d 0 4) (by simp) with h3048 | h3048
                              · linarith only [h3048, h5, hlam]
                              · rcases p3019_3 (m.d 0 5) (by simp) with h3050 | h3050
                                · linarith only [h3050, h6, hlam]
                                · linarith only [h2142, h3050, hlam]
                          · linarith only [h3045, h5, hlam]
                        · linarith only [h2, h3044, hlam]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h2675, h2676, h3011, h6, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3019_1]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h1, hlam, p3019_1]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h4, hlam, p3019_1]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [hlam, p3019_0]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h7, hlam, p3019_1]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h2063, hlam, p3019_1]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h2, hlam, p3019_0]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h5, hlam, p3019_0]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h3017, h7, hc03, hc45, hlam, hphi, ht34, p3019_1]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [hlam, p3019_0]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h2142, hlam, p3019_0]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h3, hlam, p3019_0]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [h6, hlam, p3019_1]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        rcases p3019_3 (m.d 0 1) (by simp) with h3068 | h3068
                        · rcases p3019_3 (m.d 0 2) (by simp) with h3069 | h3069
                          · rcases p3019_3 (m.d 0 3) (by simp) with h3070 | h3070
                            · linarith only [h2063, h3070, hlam]
                            · rcases p3019_3 (m.d 0 4) (by simp) with h3072 | h3072
                              · linarith only [h2142, h3072, hlam]
                              · linarith only [h3072, h7, hlam]
                          · linarith only [h3069, h4, hlam]
                        · linarith only [h1, h3068, hlam]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        rcases p3019_3 (m.d 0 1) (by simp) with h3077 | h3077
                        · rcases p3019_3 (m.d 0 2) (by simp) with h3078 | h3078
                          · rcases p3019_3 (m.d 0 3) (by simp) with h3079 | h3079
                            · linarith only [h2063, h3079, hlam]
                            · rcases p3019_3 (m.d 0 4) (by simp) with h3081 | h3081
                              · linarith only [h2142, h3081, hlam]
                              · rcases p3019_3 (m.d 0 5) (by simp) with h3083 | h3083
                                · rcases h2bigk with h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c | h3084c
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    rcases p3084_3 (m.d 0 2) (by simp) with h3086 | h3086
                                    · rcases p3084_3 (m.d 1 2) (by simp) with h3087 | h3087
                                      · linarith only [h0, h3087, hlam]
                                      · rcases p3084_3 (m.d 2 3) (by simp) with h3089 | h3089
                                        · linarith only [h3089, h4, hlam]
                                        · rcases p3084_3 (m.d 2 4) (by simp) with h3091 | h3091
                                          · linarith only [h3091, h5, hlam]
                                          · rcases p3084_3 (m.d 2 5) (by simp) with h3093 | h3093
                                            · linarith only [h3093, h6, hlam]
                                            · linarith only [h2676, h3093, hlam]
                                    · linarith only [h0, h3086, hlam]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h2675, h2676, h3011, h6, hlam, p3084_2]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h2675, h2676, h6, hlam, p3084_2]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h2675, h2676, h3011, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3084_1]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h0, hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h0, h2676, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3084_1]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h2063, h2676, h3011, h6, hc23, hc35, hlam, hphi, p3084_1]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h2676, hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h4, hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h2674, hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h3011, hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h3013, hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h5, hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h2675, hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h3017, h5, h7, hc23, hc45, hlam, hphi, ht34, p3084_1]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h3015, hlam, p3084_1]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h6, hlam, p3084_0]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [h0, h2674, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3084_1]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    rcases p3084_3 (m.d 0 2) (by simp) with h3117 | h3117
                                    · rcases p3084_3 (m.d 1 2) (by simp) with h3118 | h3118
                                      · linarith only [h2676, h3118, hlam]
                                      · linarith only [h2674, h3118, hlam]
                                    · linarith only [h3117, h4, hlam]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    rcases p3084_3 (m.d 0 2) (by simp) with h3122 | h3122
                                    · rcases p3084_3 (m.d 1 2) (by simp) with h3123 | h3123
                                      · linarith only [h2676, h3123, hlam]
                                      · linarith only [h2675, h3123, hlam]
                                    · linarith only [h3122, h5, hlam]
                                  · have p3084_0 := h3084c.1
                                    have p3084_1 := h3084c.2.1
                                    have p3084_2 := h3084c.2.2.1
                                    have p3084_3 := h3084c.2.2.2
                                    linarith only [hlam, p3084_0]
                                · linarith only [h2142, h3083, hlam]
                          · linarith only [h3078, h5, hlam]
                        · linarith only [h2, h3077, hlam]
                      · have p3019_0 := h3019c.1
                        have p3019_1 := h3019c.2.1
                        have p3019_2 := h3019c.2.2.1
                        have p3019_3 := h3019c.2.2.2
                        linarith only [hlam, p3019_0]
    · linarith only [h2142, h2674, h2675, h5, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h3133 | h3133
    · linarith only [h2142, h2674, h3133, h4, h7, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3135 | h3135
      · linarith only [h2142, h2674, h3135, h4, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3137 | h3137
        · linarith only [h1, h2674, h3137, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3139 | h3139
          · linarith only [h2063, h2674, h3139, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3141 | h3141
            · linarith only [h2142, h3133, h3141, h5, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3143 | h3143
              · linarith only [h3143, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3145 | h3145
                · linarith only [h2063, h3145, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3147 | h3147
                  · linarith only [h2142, h3147, h5, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3149 | h3149
                    · linarith only [h2142, h2674, h3149, h4, h7, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h2674, h3149, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2063 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h2142 | h2142
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h2063 h2142
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h2063 h2142

set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h2063 | h2063
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h2063
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h2063

set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7

set_option maxHeartbeats 6570000 in
set_option maxHeartbeats 6570000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s5 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3152 | h3152
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3153 | h3153
      · linarith only [h3153, h4, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3155 | h3155
        · linarith only [h3152, h3155, h4, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3157 | h3157
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3158 | h3158
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3159 | h3159
              · linarith only [h0, h3159, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3161 | h3161
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3162 | h3162
                  · linarith only [h1, h3153, h3162, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3164 | h3164
                    · linarith only [h2, h3155, h3164, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3166 | h3166
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3167 | h3167
                        · linarith only [h0, h3157, h3167, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3169 | h3169
                          · linarith only [h0, h3155, h3157, h3166, h3167, h3169, h6, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h3157, h3166, h3169, h6, hc34, hc45, hlam, hphi]
                      · linarith only [h3152, h3153, h3166, hc23, hc35, hlam, hphi]
                · linarith only [h3152, h3153, h3161, hc13, hc35, hlam, hphi]
            · linarith only [h3158, h5, h6, hc12, hc25, hlam, hphi]
          · linarith only [h3157, h4, h6, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3176 | h3176
      · linarith only [h3152, h3176, h5, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3178 | h3178
        · linarith only [h3178, h5, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3180 | h3180
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3181 | h3181
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3182 | h3182
              · linarith only [h0, h3182, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3184 | h3184
                · linarith only [h1, h3152, h3184, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3186 | h3186
                  · linarith only [h1, h3176, h3186, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3188 | h3188
                    · linarith only [h2, h3178, h3188, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3190 | h3190
                      · linarith only [h3152, h3190, h4, h6, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3192 | h3192
                        · linarith only [h3176, h3192, h4, h6, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3194 | h3194
                          · linarith only [h0, h3181, h3194, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3196 | h3196
                            · linarith only [h0, h3181, h3190, h3194, h3196, h6, hc23, hc34, hlam, hphi]
                            · rcases h0bigk with h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [hlam, p3198_0]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                rcases p3198_3 (m.d 0 1) (by simp) with h3200 | h3200
                                · rcases p3198_3 (m.d 0 2) (by simp) with h3201 | h3201
                                  · linarith only [h0, h3201, hlam]
                                  · rcases p3198_3 (m.d 0 3) (by simp) with h3203 | h3203
                                    · linarith only [h1, h3203, hlam]
                                    · rcases p3198_3 (m.d 0 4) (by simp) with h3205 | h3205
                                      · linarith only [h2, h3205, hlam]
                                      · rcases p3198_3 (m.d 0 5) (by simp) with h3207 | h3207
                                        · linarith only [h3, h3207, hlam]
                                        · linarith only [h3207, h6, hlam]
                                · linarith only [h0, h3200, hlam]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                rcases p3198_3 (m.d 0 1) (by simp) with h3211 | h3211
                                · rcases p3198_3 (m.d 0 2) (by simp) with h3212 | h3212
                                  · linarith only [h0, h3212, hlam]
                                  · linarith only [h3212, h4, hlam]
                                · linarith only [h1, h3211, hlam]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                rcases p3198_3 (m.d 0 1) (by simp) with h3216 | h3216
                                · rcases p3198_3 (m.d 0 2) (by simp) with h3217 | h3217
                                  · linarith only [h0, h3217, hlam]
                                  · linarith only [h3217, h5, hlam]
                                · linarith only [h2, h3216, hlam]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                rcases p3198_3 (m.d 0 1) (by simp) with h3221 | h3221
                                · rcases p3198_3 (m.d 0 2) (by simp) with h3222 | h3222
                                  · linarith only [h0, h3222, hlam]
                                  · rcases p3198_3 (m.d 0 3) (by simp) with h3224 | h3224
                                    · linarith only [h1, h3224, hlam]
                                    · rcases p3198_3 (m.d 0 4) (by simp) with h3226 | h3226
                                      · linarith only [h2, h3226, hlam]
                                      · rcases p3198_3 (m.d 0 5) (by simp) with h3228 | h3228
                                        · linarith only [h3, h3228, hlam]
                                        · rcases h2bigk with h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c | h3230c
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h3181, h3190, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3230_1]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3198_1, p3230_1]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3198_1, p3230_1]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h6, hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h0, hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3198_1, p3230_1]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h0, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3198_1, p3230_1]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h3182, hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h4, hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h3180, hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h3190, hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h3192, hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h5, hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h3181, hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3198_1, p3230_1]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [hlam, p3230_0]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h3194, hlam, p3230_1]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h3192, h4, hc23, hc35, hlam, hphi, p3230_1]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [h3180, h3192, hc23, hc35, hlam, hphi, p3230_1]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            rcases p3230_3 (m.d 0 2) (by simp) with h3253 | h3253
                                            · linarith only [h3253, h6, hlam]
                                            · linarith only [h3253, h4, hlam]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            rcases p3230_3 (m.d 0 2) (by simp) with h3256 | h3256
                                            · linarith only [h3256, h6, hlam]
                                            · linarith only [h3256, h5, hlam]
                                          · have p3230_0 := h3230c.1
                                            have p3230_1 := h3230c.2.1
                                            have p3230_2 := h3230c.2.2.1
                                            have p3230_3 := h3230c.2.2.2
                                            linarith only [hlam, p3230_0]
                                · linarith only [h3, h3221, hlam]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h0, hlam, p3198_0]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [hlam, p3198_0]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h1, h3192, h3196, h6, hc13, hc45, hlam, hphi, ht34, p3198_1]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h3192, h3196, h6, hc04, hc45, hlam, hphi, p3198_1]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h6, hlam, p3198_0]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h1, hlam, p3198_1]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h4, hlam, p3198_1]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [hlam, p3198_0]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h3152, hlam, p3198_1]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h3176, hlam, p3198_1]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h2, hlam, p3198_0]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h5, hlam, p3198_0]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h1, h3192, h3196, h5, h6, hc13, hc45, hlam, hphi, ht34, p3198_1]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [hlam, p3198_0]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h3178, hlam, p3198_0]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h3, hlam, p3198_0]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [h3192, h3196, h5, h6, hc24, hc45, hlam, hphi, p3198_1]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                rcases p3198_3 (m.d 0 1) (by simp) with h3278 | h3278
                                · rcases p3198_3 (m.d 0 2) (by simp) with h3279 | h3279
                                  · linarith only [h3279, h6, hlam]
                                  · linarith only [h3279, h4, hlam]
                                · linarith only [h1, h3278, hlam]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                rcases p3198_3 (m.d 0 1) (by simp) with h3283 | h3283
                                · rcases p3198_3 (m.d 0 2) (by simp) with h3284 | h3284
                                  · linarith only [h3284, h6, hlam]
                                  · linarith only [h3284, h5, hlam]
                                · linarith only [h2, h3283, hlam]
                              · have p3198_0 := h3198c.1
                                have p3198_1 := h3198c.2.1
                                have p3198_2 := h3198c.2.2.1
                                have p3198_3 := h3198c.2.2.2
                                linarith only [hlam, p3198_0]
            · linarith only [h3181, h5, h6, hc12, hc25, hlam, hphi]
          · linarith only [h3180, h4, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 6942000 in
set_option maxHeartbeats 6942000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s4 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s5 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3291 | h3291
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3292 | h3292
      · linarith only [h3292, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3294 | h3294
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3295 | h3295
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3296 | h3296
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3297 | h3297
              · linarith only [h0, h3294, h3297, h4, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3299 | h3299
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3300 | h3300
                  · linarith only [h0, h3292, h3294, h3296, h3300, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3302 | h3302
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3303 | h3303
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3304 | h3304
                        · linarith only [h2, h3292, h3296, h3297, h3304, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3306 | h3306
                          · linarith only [h0, h3296, h3304, h3306, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h1, h3302, h3304, h3306, h4, h5, hc23, hc34, hlam, hphi]
                      · linarith only [h3292, h3294, h3295, h3296, h3297, h3303, hc23, hc34, hlam, hphi]
                    · linarith only [h3292, h3294, h3302, hc13, hc34, hlam, hphi]
                · linarith only [h3291, h3299, h5, hc12, hc24, hlam, hphi]
            · linarith only [h3296, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h3294, h3295, h4, h5, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3314 | h3314
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3315 | h3315
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3316 | h3316
              · linarith only [h0, h3316, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3318 | h3318
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3319 | h3319
                  · linarith only [h1, h3292, h3319, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3321 | h3321
                    · linarith only [h1, h3294, h3321, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3323 | h3323
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3324 | h3324
                        · linarith only [h1, h3292, h3324, h4, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3326 | h3326
                          · linarith only [h1, h3294, h3315, h3326, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3328 | h3328
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3329 | h3329
                              · rcases h0bigk with h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c | h3330c
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [hlam, p3330_0]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h3291, h3328, hc01, hlam, hphi, ht0b, ht5b, p3330_1, u5ehi4]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  rcases p3330_3 (m.d 0 1) (by simp) with h3333 | h3333
                                  · rcases p3330_3 (m.d 0 2) (by simp) with h3334 | h3334
                                    · linarith only [h0, h3334, hlam]
                                    · linarith only [h3334, h4, hlam]
                                  · linarith only [h1, h3333, hlam]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h0, h3318, h3328, h5, hc01, hlam, hphi, ht0b, ht5b, p3330_1, u5ehi4]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  rcases p3330_3 (m.d 0 1) (by simp) with h3339 | h3339
                                  · rcases p3330_3 (m.d 0 2) (by simp) with h3340 | h3340
                                    · linarith only [h0, h3340, hlam]
                                    · linarith only [h3291, h3340, hlam]
                                  · linarith only [h3, h3339, hlam]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h0, hlam, p3330_0]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [hlam, p3330_0]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h1, h3315, h3324, h5, hc23, hc34, hlam, hphi, p3330_1]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h5, hlam, p3330_1]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h3, h3318, h3324, h3328, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3330_1, u5ehi4]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h1, hlam, p3330_1]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h4, hlam, p3330_1]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [hlam, p3330_0]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h3292, hlam, p3330_1]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h3294, hlam, p3330_1]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h2, hlam, p3330_0]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h0, h3318, h3328, hc04, hlam, hphi, ht0b, ht5b, p3330_1, u5ehi4]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  rcases p3330_3 (m.d 0 1) (by simp) with h3356 | h3356
                                  · rcases p3330_3 (m.d 0 2) (by simp) with h3357 | h3357
                                    · linarith only [h3357, h5, hlam]
                                    · linarith only [h3357, h4, hlam]
                                  · linarith only [h1, h3356, hlam]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [hlam, p3330_0]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  rcases p3330_3 (m.d 0 1) (by simp) with h3362 | h3362
                                  · rcases p3330_3 (m.d 0 2) (by simp) with h3363 | h3363
                                    · linarith only [h3363, h5, hlam]
                                    · linarith only [h3291, h3363, hlam]
                                  · linarith only [h3, h3362, hlam]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h3, hlam, p3330_0]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h3291, hlam, p3330_1]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h1, h3291, h3315, h3324, h5, hc23, hc34, hlam, hphi, p3330_1]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [h3314, hlam, p3330_1]
                                · have p3330_0 := h3330c.1
                                  have p3330_1 := h3330c.2.1
                                  have p3330_2 := h3330c.2.2.1
                                  have p3330_3 := h3330c.2.2.2
                                  linarith only [hlam, p3330_0]
                              · linarith only [h0, h3318, h3324, h3328, h3329, h5, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h0, h3318, h3328, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · linarith only [h3291, h3314, h3316, h3318, h3323, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h3291, h3318, h5, hc12, hc24, hlam, hphi]
            · linarith only [h3315, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h3291, h3314, h5, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3378 | h3378
      · linarith only [h3378, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3380 | h3380
        · linarith only [h3291, h3380, h4, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3382 | h3382
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3383 | h3383
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3384 | h3384
              · linarith only [h0, h3384, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3386 | h3386
                · linarith only [h0, h3291, h3386, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3388 | h3388
                  · linarith only [h1, h3378, h3388, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3390 | h3390
                    · linarith only [h1, h3291, h3380, h3390, h4, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3392 | h3392
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3393 | h3393
                        · linarith only [h0, h1, h3378, h3383, h3393, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3395 | h3395
                          · linarith only [h3291, h3380, h3395, h4, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3397 | h3397
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3398 | h3398
                              · rcases h0bigk with h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [hlam, p3399_0]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  rcases p3399_3 (m.d 0 1) (by simp) with h3401 | h3401
                                  · rcases p3399_3 (m.d 0 2) (by simp) with h3402 | h3402
                                    · linarith only [h0, h3402, hlam]
                                    · rcases p3399_3 (m.d 0 3) (by simp) with h3404 | h3404
                                      · linarith only [h1, h3404, hlam]
                                      · rcases p3399_3 (m.d 0 4) (by simp) with h3406 | h3406
                                        · linarith only [h2, h3406, hlam]
                                        · linarith only [h3406, h5, hlam]
                                  · linarith only [h0, h3401, hlam]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  rcases p3399_3 (m.d 0 1) (by simp) with h3410 | h3410
                                  · rcases p3399_3 (m.d 0 2) (by simp) with h3411 | h3411
                                    · linarith only [h0, h3411, hlam]
                                    · linarith only [h3411, h4, hlam]
                                  · linarith only [h1, h3410, hlam]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h2, h3392, hc01, hlam, hphi, ht0b, ht5b, p3399_1, u5ehi4]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  rcases p3399_3 (m.d 0 1) (by simp) with h3416 | h3416
                                  · rcases p3399_3 (m.d 0 2) (by simp) with h3417 | h3417
                                    · linarith only [h0, h3417, hlam]
                                    · rcases p3399_3 (m.d 0 3) (by simp) with h3419 | h3419
                                      · linarith only [h1, h3419, hlam]
                                      · rcases p3399_3 (m.d 0 4) (by simp) with h3421 | h3421
                                        · linarith only [h2, h3421, hlam]
                                        · linarith only [h3382, h3421, hlam]
                                  · linarith only [h3, h3416, hlam]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h0, hlam, p3399_0]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [hlam, p3399_0]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h1, h3291, h3393, h3397, hc13, hc34, hlam, hphi, p3399_1]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h5, hlam, p3399_1]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h3291, hlam, p3399_0]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h1, hlam, p3399_1]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h4, hlam, p3399_1]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [hlam, p3399_0]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h3378, hlam, p3399_1]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h3380, hlam, p3399_1]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h2, hlam, p3399_0]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h0, h3378, h3383, hc23, hc34, hlam, hphi, p3399_1]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  rcases p3399_3 (m.d 0 1) (by simp) with h3437 | h3437
                                  · rcases p3399_3 (m.d 0 2) (by simp) with h3438 | h3438
                                    · linarith only [h3438, h5, hlam]
                                    · linarith only [h3438, h4, hlam]
                                  · linarith only [h1, h3437, hlam]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [hlam, p3399_0]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h0, h3291, h3383, h3393, h5, hc23, hc34, hlam, hphi, p3399_1]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h3, hlam, p3399_0]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h0, h3291, h3383, h3395, hc23, hc35, hlam, hphi, p3399_1]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  rcases p3399_3 (m.d 0 1) (by simp) with h3446 | h3446
                                  · rcases p3399_3 (m.d 0 2) (by simp) with h3447 | h3447
                                    · linarith only [h3291, h3447, hlam]
                                    · linarith only [h3447, h4, hlam]
                                  · linarith only [h1, h3446, hlam]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [h3382, hlam, p3399_1]
                                · have p3399_0 := h3399c.1
                                  have p3399_1 := h3399c.2.1
                                  have p3399_2 := h3399c.2.2.1
                                  have p3399_3 := h3399c.2.2.2
                                  linarith only [hlam, p3399_0]
                              · linarith only [h2, h3382, h3392, h3393, h3398, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                            · linarith only [h0, h2, h3383, h3392, h3397, h5, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3378, h3382, h3383, h3384, h3392, hc23, hc34, hlam, hphi]
            · linarith only [h3291, h3383, h4, hc12, hc25, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3457 | h3457
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3458 | h3458
              · linarith only [h0, h3458, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3460 | h3460
                · linarith only [h0, h3291, h3460, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3462 | h3462
                  · linarith only [h1, h3378, h3462, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3464 | h3464
                    · linarith only [h1, h3380, h3464, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3466 | h3466
                      · linarith only [h0, h2, h3382, h3457, h3466, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3468 | h3468
                        · linarith only [h0, h3378, h3457, h3468, h5, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3470 | h3470
                          · linarith only [h0, h3380, h3382, h3457, h3470, h5, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3472 | h3472
                            · linarith only [h0, h3382, h3457, h3468, h3472, h5, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h3457, h3472, h5, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h3457, h4, h5, hc12, hc24, hlam, hphi]

end R2N4
