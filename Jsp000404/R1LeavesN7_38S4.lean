import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1750 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2167 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2337 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2650 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2651 | h2651
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2652 | h2652
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2653 | h2653
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2654 | h2654
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2655 | h2655
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2656 | h2656
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2657 | h2657
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2658 | h2658
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2659 | h2659
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2660 | h2660
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2661 | h2661
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2662 | h2662
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2663 | h2663
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2664 | h2664
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2665 | h2665
                              · linarith only [h2650, h2662, h2665, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                              · rcases h2bigk with h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c | h2667c
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h0, hlam, p2667_1]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h0, h2662, h2664, h2665, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2667_1]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h0, h2664, h2665, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2667_1]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  rcases p2667_3 (m.d 0 2) (by simp) with h2672 | h2672
                                  · rcases p2667_3 (m.d 1 2) (by simp) with h2673 | h2673
                                    · rcases p2667_3 (m.d 2 3) (by simp) with h2674 | h2674
                                      · linarith only [h2650, h2674, hlam]
                                      · linarith only [h2663, h2674, hlam]
                                    · linarith only [h2658, h2673, hlam]
                                  · linarith only [h2672, hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2650, h2662, h2664, h2665, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2667_1]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2662, h2664, h2665, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2667_1]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2664, h2665, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2667_1]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  rcases p2667_3 (m.d 0 2) (by simp) with h2683 | h2683
                                  · linarith only [h0, h2683, hlam]
                                  · linarith only [h2652, h2683, hlam]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2650, hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2656, hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2650, h2664, h2665, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2667_1]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h0, h2650, h2664, h2665, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2667_1]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2651, hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2657, hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2662, hlam, p2667_1]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h0, h2651, h2664, h2665, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2667_1]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2652, hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2658, hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2663, hlam, p2667_1]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [h2664, hlam, p2667_0]
                                · have p2667_0 := h2667c.1
                                  have p2667_1 := h2667c.2.1
                                  have p2667_2 := h2667c.2.2.1
                                  have p2667_3 := h2667c.2.2.2
                                  linarith only [hlam, p2667_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2701 | h2701
                              · linarith only [h0, h2650, h2662, h2664, h2701, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases h2bigk with h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h0, hlam, p2703_1]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h0, h2663, hc12, hlam, hphi, ht01, ht0b, ht5b, p2703_1, u5ehi8]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  rcases p2703_3 (m.d 0 2) (by simp) with h2707 | h2707
                                  · rcases p2703_3 (m.d 1 2) (by simp) with h2708 | h2708
                                    · rcases p2703_3 (m.d 2 3) (by simp) with h2709 | h2709
                                      · linarith only [h2650, h2709, hlam]
                                      · linarith only [h2662, h2709, hlam]
                                    · linarith only [h2657, h2708, hlam]
                                  · linarith only [h2707, hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  rcases p2703_3 (m.d 0 2) (by simp) with h2714 | h2714
                                  · rcases p2703_3 (m.d 1 2) (by simp) with h2715 | h2715
                                    · rcases p2703_3 (m.d 2 3) (by simp) with h2716 | h2716
                                      · linarith only [h2650, h2716, hlam]
                                      · linarith only [h2663, h2716, hlam]
                                    · linarith only [h2658, h2715, hlam]
                                  · linarith only [h2714, hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2650, h2663, hc12, hlam, hphi, ht01, ht0b, ht5b, p2703_1, u5ehi8]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2663, hc12, hlam, hphi, ht01, ht0b, ht5b, p2703_1, u5ehi8]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  rcases p2703_3 (m.d 0 2) (by simp) with h2724 | h2724
                                  · linarith only [h0, h2724, hlam]
                                  · linarith only [h2651, h2724, hlam]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  rcases p2703_3 (m.d 0 2) (by simp) with h2727 | h2727
                                  · linarith only [h0, h2727, hlam]
                                  · linarith only [h2652, h2727, hlam]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2650, hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2656, hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  rcases p2703_3 (m.d 0 2) (by simp) with h2733 | h2733
                                  · rcases p2703_3 (m.d 1 2) (by simp) with h2734 | h2734
                                    · rcases p2703_3 (m.d 2 3) (by simp) with h2735 | h2735
                                      · rcases p2703_3 (m.d 2 4) (by simp) with h2736 | h2736
                                        · linarith only [h2662, h2736, hlam]
                                        · rcases p2703_3 (m.d 2 5) (by simp) with h2738 | h2738
                                          · linarith only [h2663, h2738, hlam]
                                          · linarith only [h2664, h2738, hlam]
                                      · linarith only [h2662, h2735, hlam]
                                    · linarith only [h2657, h2734, hlam]
                                  · linarith only [h2651, h2733, hlam]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2650, hc02, hlam, hphi, ht0b, ht5b, p2703_1, u5ehi7]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2651, hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2657, hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2662, hlam, p2703_1]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2664, hlam, p2703_1]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2652, hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2658, hlam, p2703_0]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2663, hlam, p2703_1]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [h2662, hc34, hlam, hphi, ht45, p2703_1, u5elo2]
                                · have p2703_0 := h2703c.1
                                  have p2703_1 := h2703c.2.1
                                  have p2703_2 := h2703c.2.2.1
                                  have p2703_3 := h2703c.2.2.2
                                  linarith only [hlam, p2703_0]
                          · linarith only [h2662, h2663, hc34, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2756 | h2756
                          · linarith only [h1750, h2653, h2662, h2756, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2758 | h2758
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2759 | h2759
                              · rcases h2bigk with h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c | h2760c
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h0, hlam, p2760_1]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  rcases p2760_3 (m.d 0 2) (by simp) with h2763 | h2763
                                  · rcases p2760_3 (m.d 1 2) (by simp) with h2764 | h2764
                                    · rcases p2760_3 (m.d 2 3) (by simp) with h2765 | h2765
                                      · linarith only [h2765, hlam, p2760_0]
                                      · rcases p2760_3 (m.d 2 4) (by simp) with h2767 | h2767
                                        · linarith only [h2651, h2767, hlam]
                                        · linarith only [h2662, h2767, hlam]
                                    · linarith only [h2656, h2764, hlam]
                                  · linarith only [h2763, hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h0, h2758, hc12, hlam, hphi, ht01, ht0b, ht5b, p2760_1, u5ehi9]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  rcases p2760_3 (m.d 0 2) (by simp) with h2773 | h2773
                                  · rcases p2760_3 (m.d 1 2) (by simp) with h2774 | h2774
                                    · rcases p2760_3 (m.d 2 3) (by simp) with h2775 | h2775
                                      · linarith only [h2650, h2775, hlam]
                                      · rcases p2760_3 (m.d 2 4) (by simp) with h2777 | h2777
                                        · linarith only [h2651, h2777, hlam]
                                        · linarith only [h2758, h2777, hlam]
                                    · linarith only [h2658, h2774, hlam]
                                  · linarith only [h2773, hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2651, h2758, hc12, hlam, hphi, ht01, ht0b, ht5b, p2760_1, u5ehi9]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  rcases p2760_3 (m.d 0 2) (by simp) with h2784 | h2784
                                  · linarith only [h0, h2784, hlam]
                                  · linarith only [h2650, h2784, hlam]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2758, hc12, hlam, hphi, ht01, ht0b, ht5b, p2760_1, u5ehi9]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  rcases p2760_3 (m.d 0 2) (by simp) with h2788 | h2788
                                  · linarith only [h0, h2788, hlam]
                                  · linarith only [h2652, h2788, hlam]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2650, hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2656, hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2662, hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2756, hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2651, hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2657, hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  rcases p2760_3 (m.d 0 2) (by simp) with h2798 | h2798
                                  · rcases p2760_3 (m.d 1 2) (by simp) with h2799 | h2799
                                    · rcases p2760_3 (m.d 2 3) (by simp) with h2800 | h2800
                                      · linarith only [h2662, h2800, hlam]
                                      · rcases p2760_3 (m.d 2 4) (by simp) with h2802 | h2802
                                        · rcases p2760_3 (m.d 2 5) (by simp) with h2803 | h2803
                                          · linarith only [h2758, h2803, hlam]
                                          · linarith only [h2756, h2803, hlam]
                                        · linarith only [h2662, h2802, hlam]
                                    · linarith only [h2656, h2799, hlam]
                                  · linarith only [h2650, h2798, hlam]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2650, h2653, h2662, hc02, hlam, hphi, ht0b, ht5b, p2760_1, u5ehi7]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2652, hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2658, hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p2760_1, u5elo2]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [h2758, hlam, p2760_0]
                                · have p2760_0 := h2760c.1
                                  have p2760_1 := h2760c.2.1
                                  have p2760_2 := h2760c.2.2.1
                                  have p2760_3 := h2760c.2.2.2
                                  linarith only [hlam, p2760_0]
                              · linarith only [h2337, h2655, h2662, h2759, hc23, hlam, hphi, ht34, ht45, u5elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2817 | h2817
                              · rcases h2bigk with h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h0, hlam, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2650, h2653, h2662, h2758, h2817, hlam, p2818_2]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2650, h2653, h2758, h2817, hlam, p2818_2]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  rcases p2818_3 (m.d 0 2) (by simp) with h2823 | h2823
                                  · rcases p2818_3 (m.d 1 2) (by simp) with h2824 | h2824
                                    · rcases p2818_3 (m.d 2 3) (by simp) with h2825 | h2825
                                      · linarith only [h2650, h2825, hlam]
                                      · rcases p2818_3 (m.d 2 4) (by simp) with h2827 | h2827
                                        · linarith only [h2651, h2827, hlam]
                                        · rcases p2818_3 (m.d 2 5) (by simp) with h2829 | h2829
                                          · linarith only [h2829, hlam, p2818_0]
                                          · rcases h3bigk with h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c | h2831c
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h1750, hlam, p2831_1]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2653, h2662, h2758, h2817, hlam, p2831_2]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h0, h2650, h2662, h2758, h2817, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2831_1]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              rcases p2831_3 (m.d 0 3) (by simp) with h2836 | h2836
                                              · rcases p2831_3 (m.d 1 3) (by simp) with h2837 | h2837
                                                · rcases p2831_3 (m.d 2 3) (by simp) with h2838 | h2838
                                                  · linarith only [h2650, h2838, hlam]
                                                  · rcases p2831_3 (m.d 3 4) (by simp) with h2840 | h2840
                                                    · linarith only [h2653, h2840, hlam]
                                                    · linarith only [h2817, h2840, hlam]
                                                · linarith only [h2660, h2837, hlam]
                                              · linarith only [h2836, hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2653, h2656, h2662, h2758, h2817, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2831_1]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h1750, h2653, h2662, h2758, h2817, hlam, p2831_2]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2662, h2758, h2817, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2831_1]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              rcases p2831_3 (m.d 0 3) (by simp) with h2849 | h2849
                                              · linarith only [h1750, h2849, hlam]
                                              · linarith only [h2654, h2849, hlam]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2650, hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2656, hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2662, hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2756, hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2653, hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2659, hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              rcases p2831_3 (m.d 0 3) (by simp) with h2859 | h2859
                                              · rcases p2831_3 (m.d 1 3) (by simp) with h2860 | h2860
                                                · rcases p2831_3 (m.d 2 3) (by simp) with h2861 | h2861
                                                  · linarith only [h2861, hlam, p2831_0]
                                                  · rcases p2831_3 (m.d 3 4) (by simp) with h2863 | h2863
                                                    · rcases p2831_3 (m.d 3 5) (by simp) with h2864 | h2864
                                                      · linarith only [h2817, h2864, hlam]
                                                      · linarith only [h2756, h2864, hlam]
                                                    · linarith only [h2863, hlam, p2831_0]
                                                · linarith only [h2656, h2860, hlam]
                                              · linarith only [h2650, h2859, hlam]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2653, h2662, h2758, h2817, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2831_1]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2654, hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2660, hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [hc23, hlam, hphi, ht34, ht45, p2831_1, u5elo3]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [h2817, hlam, p2831_0]
                                            · have p2831_0 := h2831c.1
                                              have p2831_1 := h2831c.2.1
                                              have p2831_2 := h2831c.2.2.1
                                              have p2831_3 := h2831c.2.2.2
                                              linarith only [hlam, p2831_0]
                                    · linarith only [h2658, h2824, hlam]
                                  · linarith only [h2823, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2652, hc12, hlam, hphi, ht01, ht0b, ht5b, p2818_1, u5ehi7]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h0, h2650, h2653, h2662, h2758, h2817, hlam, p2818_2]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h0, h2650, h2653, h2758, h2817, hlam, p2818_2]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  rcases p2818_3 (m.d 0 2) (by simp) with h2883 | h2883
                                  · linarith only [h0, h2883, hlam]
                                  · linarith only [h2652, h2883, hlam]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2650, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2656, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2662, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2756, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2651, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2657, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2650, h2653, h2758, h2817, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2758, hlam, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2652, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h2658, hlam, p2818_0]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p2818_1, u5elo2]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [h0, h2650, h2653, h2758, h2817, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2818_1]
                                · have p2818_0 := h2818c.1
                                  have p2818_1 := h2818c.2.1
                                  have p2818_2 := h2818c.2.2.1
                                  have p2818_3 := h2818c.2.2.2
                                  linarith only [hlam, p2818_0]
                              · linarith only [h2337, h2655, h2662, h2817, hc23, hlam, hphi, ht34, ht45, u5elo1]
                      · linarith only [h2167, h2655, h2661, hlam]
                    · linarith only [h1750, h2337, h2654, h2660, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h1750, h2653, h2659, hlam]
                · linarith only [h0, h2337, h2652, h2658, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
              · linarith only [h0, h2651, h2657, hlam]
            · linarith only [h0, h2650, h2656, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2908 | h2908
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2909 | h2909
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2910 | h2910
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2911 | h2911
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2912 | h2912
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2913 | h2913
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2914 | h2914
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2915 | h2915
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2916 | h2916
                            · linarith only [h2651, h2655, h2916, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2918 | h2918
                              · linarith only [h2651, h2655, h2914, h2918, hlam]
                              · rcases h2bigk with h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c | h2920c
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h0, hlam, p2920_1]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2915, hc02, hlam, hphi, ht0b, ht5b, p2920_1, u5ehi8]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  rcases p2920_3 (m.d 0 2) (by simp) with h2924 | h2924
                                  · rcases p2920_3 (m.d 1 2) (by simp) with h2925 | h2925
                                    · rcases p2920_3 (m.d 2 3) (by simp) with h2926 | h2926
                                      · linarith only [h2650, h2926, hlam]
                                      · linarith only [h2914, h2926, hlam]
                                    · linarith only [h2909, h2925, hlam]
                                  · linarith only [h2924, hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  rcases p2920_3 (m.d 0 2) (by simp) with h2931 | h2931
                                  · rcases p2920_3 (m.d 1 2) (by simp) with h2932 | h2932
                                    · rcases p2920_3 (m.d 2 3) (by simp) with h2933 | h2933
                                      · linarith only [h2650, h2933, hlam]
                                      · linarith only [h2915, h2933, hlam]
                                    · linarith only [h2910, h2932, hlam]
                                  · linarith only [h2931, hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2167, h2650, h2655, h2913, h2915, hc01, hc12, hlam, hphi, p2920_1, u5ehi8, u5elo1]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2167, h2655, h2913, h2915, hc01, hc12, hlam, hphi, p2920_1, u5ehi8, u5elo1]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  rcases p2920_3 (m.d 0 2) (by simp) with h2941 | h2941
                                  · linarith only [h0, h2941, hlam]
                                  · linarith only [h2651, h2941, hlam]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  rcases p2920_3 (m.d 0 2) (by simp) with h2944 | h2944
                                  · linarith only [h0, h2944, hlam]
                                  · linarith only [h2652, h2944, hlam]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2650, hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2908, hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  rcases p2920_3 (m.d 0 2) (by simp) with h2950 | h2950
                                  · rcases p2920_3 (m.d 1 2) (by simp) with h2951 | h2951
                                    · rcases p2920_3 (m.d 2 3) (by simp) with h2952 | h2952
                                      · rcases p2920_3 (m.d 2 4) (by simp) with h2953 | h2953
                                        · linarith only [h2914, h2953, hlam]
                                        · rcases p2920_3 (m.d 2 5) (by simp) with h2955 | h2955
                                          · linarith only [h2915, h2955, hlam]
                                          · linarith only [h2916, h2955, hlam]
                                      · linarith only [h2914, h2952, hlam]
                                    · linarith only [h2909, h2951, hlam]
                                  · linarith only [h2651, h2950, hlam]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2650, h2915, hc02, hlam, hphi, ht0b, ht5b, p2920_1, u5ehi8]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2651, hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2909, hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2914, hlam, p2920_1]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2916, hlam, p2920_1]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2652, hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2910, hlam, p2920_0]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2915, hlam, p2920_1]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [h2914, hc34, hlam, hphi, ht45, p2920_1, u5elo2]
                                · have p2920_0 := h2920c.1
                                  have p2920_1 := h2920c.2.1
                                  have p2920_2 := h2920c.2.2.1
                                  have p2920_3 := h2920c.2.2.2
                                  linarith only [hlam, p2920_0]
                          · linarith only [h2654, h2655, h2913, h2914, h2915, hc34, hlam, hphi, ht45, u5elo1]
                        · linarith only [h2653, h2655, h2913, h2914, hc23, hlam, hphi, ht34, ht45, u5elo1]
                      · linarith only [h2167, h2913, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h1750, h2337, h2654, h2912, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h1750, h2653, h2655, h2911, hc03, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h2337, h2652, h2910, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
              · linarith only [h0, h2651, h2909, hlam]
            · linarith only [h0, h2650, h2908, hlam]
        · linarith only [h2653, h2654, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2981 | h2981
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2982 | h2982
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2983 | h2983
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2984 | h2984
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2985 | h2985
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2986 | h2986
                  · linarith only [h2653, h2981, h2986, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2988 | h2988
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2989 | h2989
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2990 | h2990
                        · linarith only [h1750, h2986, h2990, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2992 | h2992
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2993 | h2993
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2994 | h2994
                              · rcases h2bigk with h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h0, hlam, p2995_1]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2992, h2994, hc02, hlam, hphi, ht0b, ht5b, p2995_1, u5ehi9]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h0, h2990, h2992, h2994, hc12, hlam, hphi, ht01, ht0b, ht5b, p2995_1, u5ehi9]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  rcases p2995_3 (m.d 0 2) (by simp) with h3000 | h3000
                                  · rcases p2995_3 (m.d 1 2) (by simp) with h3001 | h3001
                                    · rcases p2995_3 (m.d 2 3) (by simp) with h3002 | h3002
                                      · linarith only [h2650, h3002, hlam]
                                      · linarith only [h2992, h3002, hlam]
                                    · linarith only [h2985, h3001, hlam]
                                  · linarith only [h3000, hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2650, h2992, h2994, hc12, hlam, hphi, ht01, ht0b, ht5b, p2995_1, u5ehi9]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2992, h2994, hc12, hlam, hphi, ht01, ht0b, ht5b, p2995_1, u5ehi9]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2990, h2992, h2994, hc12, hlam, hphi, ht01, ht0b, ht5b, p2995_1, u5ehi9]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  rcases p2995_3 (m.d 0 2) (by simp) with h3011 | h3011
                                  · linarith only [h0, h3011, hlam]
                                  · linarith only [h2652, h3011, hlam]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2650, hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2983, hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2990, hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h1750, h2650, h2986, h2992, h2994, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2995_1, u5ehi9]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2651, hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2984, hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h0, h2651, h2992, h2994, hc12, hlam, hphi, ht01, ht0b, ht5b, p2995_1, u5ehi9]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h0, h2651, h2992, h2994, hc12, hlam, hphi, ht01, ht0b, ht5b, p2995_1, u5ehi9]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2652, hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2985, hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2992, hlam, p2995_1]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [h2993, hlam, p2995_0]
                                · have p2995_0 := h2995c.1
                                  have p2995_1 := h2995c.2.1
                                  have p2995_2 := h2995c.2.2.1
                                  have p2995_3 := h2995c.2.2.2
                                  linarith only [hlam, p2995_0]
                              · linarith only [h1750, h2986, h2994, hc03, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h2337, h2982, h2990, h2992, h2993, hlam, hphi, u5ehi8, u5elo1]
                          · linarith only [h1750, h2981, h2986, h2992, hc23, hc34, hlam, hphi]
                      · linarith only [h2167, h2337, h2982, h2989, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                    · linarith only [h1750, h2988, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h2652, h2985, hlam]
              · linarith only [h0, h2651, h2984, hlam]
            · linarith only [h0, h2650, h2983, hlam]
          · linarith only [h2653, h2981, h2982, hlam, hphi, u5ehi8, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3038 | h3038
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3039 | h3039
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3040 | h3040
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3041 | h3041
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3042 | h3042
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3043 | h3043
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3044 | h3044
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3045 | h3045
                        · linarith only [h2650, h2653, h2981, h3038, h3043, h3045, hlam, hphi, u5ehi9, u5elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3047 | h3047
                          · linarith only [h2650, h2981, h3047, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3049 | h3049
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3050 | h3050
                              · rcases h2bigk with h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c | h3051c
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h0, hlam, p3051_1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  rcases p3051_3 (m.d 0 2) (by simp) with h3054 | h3054
                                  · rcases p3051_3 (m.d 1 2) (by simp) with h3055 | h3055
                                    · rcases p3051_3 (m.d 2 3) (by simp) with h3056 | h3056
                                      · linarith only [h3056, hlam, p3051_0]
                                      · rcases p3051_3 (m.d 2 4) (by simp) with h3058 | h3058
                                        · linarith only [h2651, h3058, hlam]
                                        · linarith only [h3045, h3058, hlam]
                                    · linarith only [h3039, h3055, hlam]
                                  · linarith only [h3054, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h3049, hc02, hlam, hphi, ht0b, ht5b, p3051_1, u5ehi9]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  rcases p3051_3 (m.d 0 2) (by simp) with h3064 | h3064
                                  · rcases p3051_3 (m.d 1 2) (by simp) with h3065 | h3065
                                    · rcases p3051_3 (m.d 2 3) (by simp) with h3066 | h3066
                                      · linarith only [h2650, h3066, hlam]
                                      · rcases p3051_3 (m.d 2 4) (by simp) with h3068 | h3068
                                        · linarith only [h2651, h3068, hlam]
                                        · linarith only [h3049, h3068, hlam]
                                    · linarith only [h3041, h3065, hlam]
                                  · linarith only [h3064, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h1750, h2651, h2981, h3043, h3049, hc01, hc12, hlam, hphi, p3051_1, u5ehi9, u5elo1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  rcases p3051_3 (m.d 0 2) (by simp) with h3075 | h3075
                                  · linarith only [h0, h3075, hlam]
                                  · linarith only [h2650, h3075, hlam]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h1750, h2981, h3043, h3049, hc01, hc12, hlam, hphi, p3051_1, u5ehi9, u5elo1]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  rcases p3051_3 (m.d 0 2) (by simp) with h3079 | h3079
                                  · linarith only [h0, h3079, hlam]
                                  · linarith only [h2652, h3079, hlam]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2650, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h3039, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h3045, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h3047, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2651, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h3040, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  rcases p3051_3 (m.d 0 2) (by simp) with h3089 | h3089
                                  · rcases p3051_3 (m.d 1 2) (by simp) with h3090 | h3090
                                    · rcases p3051_3 (m.d 2 3) (by simp) with h3091 | h3091
                                      · linarith only [h3045, h3091, hlam]
                                      · rcases p3051_3 (m.d 2 4) (by simp) with h3093 | h3093
                                        · rcases p3051_3 (m.d 2 5) (by simp) with h3094 | h3094
                                          · linarith only [h3049, h3094, hlam]
                                          · linarith only [h3047, h3094, hlam]
                                        · linarith only [h3045, h3093, hlam]
                                    · linarith only [h3039, h3090, hlam]
                                  · linarith only [h2650, h3089, hlam]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2651, h3049, hc02, hlam, hphi, ht0b, ht5b, p3051_1, u5ehi9]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h2652, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h3041, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p3051_1, u5elo2]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [h3049, hlam, p3051_0]
                                · have p3051_0 := h3051c.1
                                  have p3051_1 := h3051c.2.1
                                  have p3051_2 := h3051c.2.2.1
                                  have p3051_3 := h3051c.2.2.2
                                  linarith only [hlam, p3051_0]
                              · linarith only [h1750, h2653, h3050, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3108 | h3108
                              · rcases h2bigk with h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h0, hlam, p3109_1]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  rcases p3109_3 (m.d 0 2) (by simp) with h3112 | h3112
                                  · rcases p3109_3 (m.d 1 2) (by simp) with h3113 | h3113
                                    · rcases p3109_3 (m.d 2 3) (by simp) with h3114 | h3114
                                      · linarith only [h3114, hlam, p3109_0]
                                      · rcases p3109_3 (m.d 2 4) (by simp) with h3116 | h3116
                                        · linarith only [h2651, h3116, hlam]
                                        · linarith only [h3045, h3116, hlam]
                                    · linarith only [h3039, h3113, hlam]
                                  · linarith only [h3112, hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  rcases p3109_3 (m.d 0 2) (by simp) with h3121 | h3121
                                  · rcases p3109_3 (m.d 1 2) (by simp) with h3122 | h3122
                                    · rcases p3109_3 (m.d 2 3) (by simp) with h3123 | h3123
                                      · linarith only [h2650, h3123, hlam]
                                      · rcases p3109_3 (m.d 2 4) (by simp) with h3125 | h3125
                                        · linarith only [h3125, hlam, p3109_0]
                                        · rcases p3109_3 (m.d 2 5) (by simp) with h3127 | h3127
                                          · linarith only [h2652, h3127, hlam]
                                          · linarith only [h3049, h3127, hlam]
                                    · linarith only [h3040, h3122, hlam]
                                  · linarith only [h3121, hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  rcases p3109_3 (m.d 0 2) (by simp) with h3132 | h3132
                                  · rcases p3109_3 (m.d 1 2) (by simp) with h3133 | h3133
                                    · rcases p3109_3 (m.d 2 3) (by simp) with h3134 | h3134
                                      · linarith only [h2650, h3134, hlam]
                                      · rcases p3109_3 (m.d 2 4) (by simp) with h3136 | h3136
                                        · linarith only [h2651, h3136, hlam]
                                        · rcases p3109_3 (m.d 2 5) (by simp) with h3138 | h3138
                                          · linarith only [h3138, hlam, p3109_0]
                                          · rcases h3bigk with h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h1750, hlam, p3140_1]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h2981, h3043, hc23, hlam, hphi, ht34, ht45, p3140_1, u5elo1]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h2653, hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h2981, hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              rcases p3140_3 (m.d 0 3) (by simp) with h3146 | h3146
                                              · linarith only [h1750, h3146, hlam]
                                              · rcases p3140_3 (m.d 1 3) (by simp) with h3148 | h3148
                                                · rcases p3140_3 (m.d 2 3) (by simp) with h3149 | h3149
                                                  · linarith only [h3039, h3149, hlam]
                                                  · rcases p3140_3 (m.d 3 4) (by simp) with h3151 | h3151
                                                    · linarith only [h3042, h3151, hlam]
                                                    · linarith only [h2653, h3151, hlam]
                                                · linarith only [h1750, h3148, hlam]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h2653, h3038, h3042, h3045, h3049, hlam, p3140_2]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h1750, h2653, h2981, h3038, h3043, h3045, h3049, hc01, hc13, hc23, hlam, hphi, ht34, ht45, p3140_1, u5elo1]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h1750, h2981, h3039, hc01, hc12, hlam, hphi, p3140_1]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h2650, hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h3039, hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h3045, hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h3047, hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h1750, h3039, h3042, hc01, hc12, hlam, hphi, p3140_1]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h3042, hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              rcases p3140_3 (m.d 0 3) (by simp) with h3166 | h3166
                                              · linarith only [h2653, h3166, hlam]
                                              · linarith only [h2650, h3166, hlam]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h1750, h2981, h3039, h3042, hc01, hc12, hlam, hphi, p3140_1]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h1750, h3043, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3140_1, u5elo1]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h3043, hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h3043, hc23, hlam, hphi, ht34, ht45, p3140_1, u5elo1]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [h3108, hlam, p3140_0]
                                            · have p3140_0 := h3140c.1
                                              have p3140_1 := h3140c.2.1
                                              have p3140_2 := h3140c.2.2.1
                                              have p3140_3 := h3140c.2.2.2
                                              linarith only [hlam, p3140_0]
                                    · linarith only [h3041, h3133, hlam]
                                  · linarith only [h3132, hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h2651, h3038, h3045, h3049, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3109_1]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h2653, h3038, h3039, h3042, h3045, h3049, hlam, p3109_2]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h2653, h3038, h3039, h3042, h3049, hlam, p3109_2]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  rcases p3109_3 (m.d 0 2) (by simp) with h3182 | h3182
                                  · linarith only [h0, h3182, hlam]
                                  · linarith only [h2652, h3182, hlam]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h2650, hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h3039, hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h3045, hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h3047, hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h2651, hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h3040, hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h2651, h3038, h3049, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3109_1]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h3049, hlam, p3109_1]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h2652, hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h3041, hlam, p3109_0]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h1750, h2653, h2981, h3038, h3039, h3042, h3043, h3049, hc01, hc12, hc23, hlam, hphi, ht34, ht45, p3109_1, u5elo1]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [h1750, h2653, h2981, h3038, h3039, h3042, h3043, h3049, hc01, hc12, hc24, hlam, hphi, ht45, p3109_1, u5elo1]
                                · have p3109_0 := h3109c.1
                                  have p3109_1 := h3109c.2.1
                                  have p3109_2 := h3109c.2.2.1
                                  have p3109_3 := h3109c.2.2.2
                                  linarith only [hlam, p3109_0]
                              · linarith only [h2653, h3038, h3108, hlam]
                      · linarith only [h2653, h3038, h3042, h3044, hlam]
                    · linarith only [h2653, h3038, h3042, h3043, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3203 | h3203
                    · linarith only [h1750, h2981, h3042, h3203, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1750, h3203, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h3041, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h2651, h3040, hlam]
            · linarith only [h0, h2650, h3039, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3209 | h3209
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3210 | h3210
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3211 | h3211
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3212 | h3212
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3213 | h3213
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3214 | h3214
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3215 | h3215
                        · linarith only [h2650, h2653, h3215, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3217 | h3217
                          · linarith only [h2650, h2652, h2653, h2981, h3038, h3214, h3217, hlam, hphi, u5ehi7, u5elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3219 | h3219
                            · linarith only [h2651, h3038, h3219, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3221 | h3221
                              · linarith only [h1750, h2653, h3038, h3209, h3212, h3221, hc01, hc12, hlam, hphi]
                              · linarith only [h1750, h2653, h3214, h3221, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                      · linarith only [h2167, h3214, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h1750, h3213, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3226 | h3226
                    · linarith only [h1750, h2981, h3212, h3226, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1750, h3226, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h2652, h3211, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
              · linarith only [h0, h2651, h3038, h3210, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h0, h2650, h3209, hlam]
    · linarith only [h2650, h2652, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3233 | h3233
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3234 | h3234
      · linarith only [h2650, h2651, h3234, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3236 | h3236
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3237 | h3237
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3238 | h3238
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3239 | h3239
              · linarith only [h2650, h2651, h3236, h3239, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3241 | h3241
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3242 | h3242
                  · linarith only [h3234, h3236, h3242, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3244 | h3244
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3245 | h3245
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3246 | h3246
                        · linarith only [h1750, h3242, h3246, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3248 | h3248
                          · linarith only [h0, h2650, h3239, h3246, h3248, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                          · linarith only [h0, h2650, h3236, h3239, h3246, h3248, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2650, h3236, h3237, h3239, h3245, hc04, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · linarith only [h0, h1750, h2650, h3236, h3244, hc01, hc12, hlam, hphi]
                · linarith only [h0, h2650, h3236, h3241, hlam, hphi, u5ehi8, u5elo2]
            · linarith only [h0, h2650, h3238, hlam]
          · linarith only [h2650, h2651, h3236, h3237, hlam, hphi, u5ehi8, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3256 | h3256
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3257 | h3257
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3258 | h3258
              · linarith only [h2651, h3233, h3258, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3260 | h3260
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3261 | h3261
                  · linarith only [h2651, h3233, h3234, h3257, h3258, h3261, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3263 | h3263
                    · linarith only [h1750, h3236, h3257, h3258, h3263, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h1750, h3263, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h2651, h3233, h3234, h3260, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h2650, h3257, hlam]
          · linarith only [h2651, h3233, h3256, hlam, hphi, u5ehi7, u5elo4]
    · linarith only [h2650, h3233, hc23, hlam, hphi, ht34, ht45, u5elo2]

end R2N4
