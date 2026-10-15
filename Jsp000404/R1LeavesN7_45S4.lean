import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_45S2
import Jsp000404.R1LeavesN7_45S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1448 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1632 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1864 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1866 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h2665 | h2665
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2666 | h2666
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2667 | h2667
      · linarith only [h1866, h2666, h2667, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2669 | h2669
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2670 | h2670
          · linarith only [h2667, h2670, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2672 | h2672
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2673 | h2673
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2674 | h2674
                · linarith only [h2667, h2669, h2674, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2676 | h2676
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2677 | h2677
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2678 | h2678
                      · linarith only [h1632, h2669, h2670, h2674, h2677, h2678, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2680 | h2680
                        · linarith only [h0, h2670, h2678, h2680, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h1bigk with h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h0, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1448, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1632, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1864, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h2670, hc01, hc25, hlam, hphi, ht12, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h2667, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1632, h2670, h2678, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h2670, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            rcases p2682_3 (m.d 0 1) (by simp) with h2693 | h2693
                            · linarith only [h2693, hlam, p2682_0]
                            · rcases p2682_3 (m.d 1 2) (by simp) with h2695 | h2695
                              · linarith only [h2667, h2695, hlam]
                              · linarith only [h0, h2695, hlam]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h0, h2667, hc01, hc23, hlam, hphi, ht12, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1632, h2667, hc01, hc23, hlam, hphi, ht12, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1864, h2666, h2667, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2682_1, u5ehi3]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h2667, h2669, hc01, hc23, hlam, hphi, ht12, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h2669, hlam, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h2672, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h2674, hlam, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            rcases p2682_3 (m.d 0 1) (by simp) with h2707 | h2707
                            · linarith only [h2707, hlam, p2682_0]
                            · rcases p2682_3 (m.d 1 2) (by simp) with h2709 | h2709
                              · linarith only [h2670, h2709, hlam]
                              · linarith only [h0, h2709, hlam]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h2673, hlam, p2682_0]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [h1632, hc01, hc15, hlam, hphi, p2682_1]
                          · have p2682_0 := h2682c.1
                            have p2682_1 := h2682c.2.1
                            have p2682_2 := h2682c.2.2.1
                            have p2682_3 := h2682c.2.2.2
                            linarith only [hlam, p2682_0]
                    · linarith only [h1448, h2666, h2667, h2677, hlam]
                  · linarith only [h1448, h2666, h2667, h2676, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · linarith only [h1448, h2666, h2673, hlam]
            · linarith only [h1448, h2665, h2666, h2672, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2720 | h2720
          · linarith only [h2667, h2720, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2722 | h2722
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2723 | h2723
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2724 | h2724
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2725 | h2725
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2726 | h2726
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2727 | h2727
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2728 | h2728
                        · linarith only [h2665, h2728, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases h1bigk with h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h0, hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h1448, hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h1632, hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h1864, hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h2720, h2725, h2727, hc01, hc23, hlam, hphi, ht12, p2730_1]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h2667, hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h2669, hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h2720, hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            rcases p2730_3 (m.d 0 1) (by simp) with h2741 | h2741
                            · linarith only [h2741, hlam, p2730_0]
                            · rcases p2730_3 (m.d 1 2) (by simp) with h2743 | h2743
                              · linarith only [h2667, h2743, hlam]
                              · linarith only [h0, h2743, hlam]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h0, h2667, hc01, hc23, hlam, hphi, ht12, p2730_1]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h2667, h2724, h2728, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2730_1]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h1864, h2667, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2730_1, u5ehi0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            rcases p2730_3 (m.d 0 1) (by simp) with h2750 | h2750
                            · linarith only [h2750, hlam, p2730_0]
                            · rcases p2730_3 (m.d 1 2) (by simp) with h2752 | h2752
                              · linarith only [h2669, h2752, hlam]
                              · linarith only [h0, h2752, hlam]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p2730_1]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h2722, hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h1864, h2666, h2669, h2725, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2730_1, u5ehi3]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            rcases p2730_3 (m.d 0 1) (by simp) with h2759 | h2759
                            · linarith only [h2759, hlam, p2730_0]
                            · rcases p2730_3 (m.d 1 2) (by simp) with h2761 | h2761
                              · linarith only [h2720, h2761, hlam]
                              · linarith only [h0, h2761, hlam]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p2730_1]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h2723, hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [h2724, hlam, p2730_0]
                          · have p2730_0 := h2730c.1
                            have p2730_1 := h2730c.2.1
                            have p2730_2 := h2730c.2.2.1
                            have p2730_3 := h2730c.2.2.2
                            linarith only [hlam, p2730_0]
                      · linarith only [h0, h2669, h2727, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1448, h2666, h2667, h2726, hlam]
                  · linarith only [h1448, h2666, h2667, h2725, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2771 | h2771
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2772 | h2772
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2773 | h2773
                      · linarith only [h1632, h2724, h2773, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h2669, h2773, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1448, h2666, h2667, h2772, hlam]
                  · linarith only [h1448, h2665, h2666, h2667, h2771, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h1448, h2666, h2723, hlam]
            · linarith only [h1448, h2665, h2722, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2780 | h2780
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2781 | h2781
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2782 | h2782
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2783 | h2783
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2784 | h2784
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2785 | h2785
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2786 | h2786
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2787 | h2787
                    · linarith only [h2666, h2780, h2787, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                    · linarith only [h0, h1866, h2780, h2784, h2787, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h1866, h2665, h2666, h2780, h2784, h2786, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2791 | h2791
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2792 | h2792
                    · linarith only [h2666, h2780, h2792, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                    · linarith only [h0, h1866, h2780, h2784, h2792, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h1866, h2665, h2666, h2780, h2784, h2791, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2796 | h2796
                · linarith only [h2783, h2784, h2796, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2798 | h2798
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2799 | h2799
                    · linarith only [h1448, h2784, h2799, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2801 | h2801
                      · linarith only [h1864, h2781, h2796, h2801, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2803 | h2803
                        · linarith only [h1866, h2665, h2780, h2781, h2784, h2796, h2803, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases h1bigk with h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [hlam, p2805_0]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h0, hlam, p2805_0]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h1448, hlam, p2805_0]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h1632, hlam, p2805_0]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h1864, hlam, p2805_0]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            rcases p2805_3 (m.d 0 1) (by simp) with h2811 | h2811
                            · linarith only [h2811, hlam, p2805_0]
                            · rcases p2805_3 (m.d 1 2) (by simp) with h2813 | h2813
                              · rcases p2805_3 (m.d 1 3) (by simp) with h2814 | h2814
                                · linarith only [h2780, h2814, hlam]
                                · linarith only [h1448, h2814, hlam]
                              · linarith only [h2813, hlam, p2805_0]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [hlam, p2805_0]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h1448, hc01, hc12, hlam, hphi, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h1632, hc01, hc12, hlam, hphi, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h1864, hc12, hlam, hphi, ht01, ht0b, ht5b, p2805_1, u5ehi0]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h2784, h2803, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h2780, hlam, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [hlam, p2805_0]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h1632, h2784, h2803, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h2784, hlam, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h2783, h2784, h2803, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h2781, hlam, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h2783, hlam, p2805_0]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [hlam, p2805_0]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h2796, hlam, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            rcases p2805_3 (m.d 0 1) (by simp) with h2832 | h2832
                            · linarith only [h2832, hlam, p2805_0]
                            · rcases p2805_3 (m.d 1 2) (by simp) with h2834 | h2834
                              · rcases p2805_3 (m.d 1 3) (by simp) with h2835 | h2835
                                · linarith only [h2784, h2835, hlam]
                                · linarith only [h1448, h2835, hlam]
                              · linarith only [h0, h2834, hlam]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h2782, hlam, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h1448, hc01, hc15, hlam, hphi, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [h1632, h2784, h2803, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2805_1]
                          · have p2805_0 := h2805c.1
                            have p2805_1 := h2805c.2.1
                            have p2805_2 := h2805c.2.2.1
                            have p2805_3 := h2805c.2.2.2
                            linarith only [hlam, p2805_0]
                  · linarith only [h1866, h2665, h2798, hlam]
            · linarith only [h1866, h2665, h2780, h2783, hlam]
          · linarith only [h0, h1866, h2780, h2782, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h1866, h2780, h2781, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2847 | h2847
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2848 | h2848
          · linarith only [h2780, h2848, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2850 | h2850
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2851 | h2851
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2852 | h2852
                · linarith only [h2780, h2847, h2852, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2854 | h2854
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2855 | h2855
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2856 | h2856
                      · linarith only [h2847, h2848, h2852, h2855, h2856, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2858 | h2858
                        · linarith only [h2665, h2666, h2780, h2848, h2851, h2856, h2858, hc12, hc23, hlam, hphi]
                        · rcases h1bigk with h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h0, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h1448, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h1632, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h1864, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2848, hc01, hc25, hlam, hphi, ht12, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2780, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h1632, h2848, h2856, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2848, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            rcases p2860_3 (m.d 0 1) (by simp) with h2871 | h2871
                            · linarith only [h2871, hlam, p2860_0]
                            · rcases p2860_3 (m.d 1 2) (by simp) with h2873 | h2873
                              · linarith only [h2780, h2873, hlam]
                              · linarith only [h0, h2873, hlam]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h0, h2780, hc01, hc23, hlam, hphi, ht12, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h1632, h2780, hc01, hc23, hlam, hphi, ht12, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2780, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2860_1, u5ehi1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2780, h2847, hc01, hc23, hlam, hphi, ht12, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2847, hlam, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2850, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2852, hlam, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            rcases p2860_3 (m.d 0 1) (by simp) with h2885 | h2885
                            · linarith only [h2885, hlam, p2860_0]
                            · rcases p2860_3 (m.d 1 2) (by simp) with h2887 | h2887
                              · linarith only [h2848, h2887, hlam]
                              · linarith only [h0, h2887, hlam]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2851, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h1632, h2848, h2856, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [hlam, p2860_0]
                    · linarith only [h1632, h2780, h2847, h2855, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h2665, h2666, h2780, h2851, h2854, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2896 | h2896
                · linarith only [h2780, h2847, h2896, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2898 | h2898
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2899 | h2899
                    · linarith only [h0, h2780, h2851, h2899, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h1632, h2780, h2847, h2899, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h1632, h2665, h2780, h2847, h2898, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · linarith only [h2665, h2666, h2850, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2904 | h2904
          · linarith only [h2847, h2904, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2906 | h2906
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2907 | h2907
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2908 | h2908
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2909 | h2909
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2910 | h2910
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2911 | h2911
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2912 | h2912
                        · linarith only [h2665, h2666, h2780, h2907, h2912, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases h1bigk with h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h0, hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h1448, hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h1632, hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h1864, hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h2904, h2909, h2911, hc01, hc23, hlam, hphi, ht12, p2914_1]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h2780, hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h2847, hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h2904, hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            rcases p2914_3 (m.d 0 1) (by simp) with h2925 | h2925
                            · linarith only [h2925, hlam, p2914_0]
                            · rcases p2914_3 (m.d 1 2) (by simp) with h2927 | h2927
                              · linarith only [h2780, h2927, hlam]
                              · linarith only [h0, h2927, hlam]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h0, hc01, hc13, hlam, hphi, p2914_1]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h2665, h2666, h2780, h2908, h2912, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2914_1]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h2780, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2914_1, u5ehi1]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            rcases p2914_3 (m.d 0 1) (by simp) with h2934 | h2934
                            · linarith only [h2934, hlam, p2914_0]
                            · rcases p2914_3 (m.d 1 2) (by simp) with h2936 | h2936
                              · linarith only [h2847, h2936, hlam]
                              · linarith only [h0, h2936, hlam]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p2914_1]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h2906, hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h2665, h2666, h2847, h2908, h2909, h2912, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2914_1]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            rcases p2914_3 (m.d 0 1) (by simp) with h2943 | h2943
                            · linarith only [h2943, hlam, p2914_0]
                            · rcases p2914_3 (m.d 1 2) (by simp) with h2945 | h2945
                              · linarith only [h2904, h2945, hlam]
                              · linarith only [h0, h2945, hlam]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p2914_1]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h2907, hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [h2908, hlam, p2914_0]
                          · have p2914_0 := h2914c.1
                            have p2914_1 := h2914c.2.1
                            have p2914_2 := h2914c.2.2.1
                            have p2914_3 := h2914c.2.2.2
                            linarith only [hlam, p2914_0]
                      · linarith only [h0, h2847, h2911, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h2780, h2910, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h2665, h2666, h2780, h2907, h2909, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2955 | h2955
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2956 | h2956
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2957 | h2957
                      · linarith only [h1632, h2908, h2957, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h2847, h2957, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h1866, h2907, h2956, hc01, hc13, hlam, hphi]
                  · linarith only [h2665, h2780, h2907, h2955, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2962 | h2962
                · linarith only [h2906, h2907, h2962, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2964 | h2964
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2965 | h2965
                    · linarith only [h1448, h2907, h2965, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h2780, h2965, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h2665, h2780, h2964, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · linarith only [h2665, h2666, h2906, hc13, hc35, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2970 | h2970
    · linarith only [h2665, h2970, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2972 | h2972
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2973 | h2973
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2974 | h2974
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2975 | h2975
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2976 | h2976
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2977 | h2977
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2978 | h2978
                  · linarith only [h0, h1866, h2665, h2972, h2978, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h1866, h2972, h2975, h2978, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2981 | h2981
                  · linarith only [h0, h1866, h2665, h2972, h2981, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h1866, h2972, h2975, h2981, hc01, hc12, hlam, hphi]
              · linarith only [h0, h1866, h2665, h2975, h2976, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2985 | h2985
              · linarith only [h2975, h2985, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2987 | h2987
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2988 | h2988
                  · linarith only [h1448, h2975, h2988, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2990 | h2990
                    · linarith only [h2972, h2985, h2990, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2992 | h2992
                      · linarith only [h2973, h2992, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · linarith only [h0, h1866, h2987, h2988, h2992, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2995 | h2995
                  · linarith only [h0, h1866, h2665, h2972, h2985, h2995, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2997 | h2997
                    · linarith only [h2972, h2975, h2987, h2997, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2999 | h2999
                      · linarith only [h2973, h2987, h2999, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3001 | h3001
                        · linarith only [h1448, h2975, h2987, h3001, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h1866, h2972, h2975, h3001, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h1866, h2972, h2974, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h1866, h2972, h2973, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3006 | h3006
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3007 | h3007
          · linarith only [h2972, h3007, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3009 | h3009
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3010 | h3010
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3011 | h3011
                · linarith only [h2972, h3006, h3011, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3013 | h3013
                  · linarith only [h0, h1866, h2665, h2972, h3006, h3013, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2972, h3013, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h1866, h2665, h3009, h3010, hc01, hc35, hlam, hphi, ht12, ht23]
            · linarith only [h2972, h3006, h3009, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3018 | h3018
          · linarith only [h2972, h3018, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3020 | h3020
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3021 | h3021
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3022 | h3022
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3023 | h3023
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3024 | h3024
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3025 | h3025
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3026 | h3026
                        · linarith only [h3020, h3026, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · linarith only [h0, h1866, h2665, h3022, h3026, hc01, hc14, hlam, hphi]
                      · linarith only [h3006, h3022, h3025, hlam]
                    · linarith only [h3006, h3022, h3023, h3024, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · linarith only [h0, h2972, h3023, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3032 | h3032
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3033 | h3033
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3034 | h3034
                      · linarith only [h1632, h3022, h3032, h3034, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h3006, h3034, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h1866, h3021, h3033, hc01, hc13, hlam, hphi]
                  · linarith only [h2972, h3021, h3032, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · linarith only [h0, h1866, h2665, h3020, h3021, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3040 | h3040
              · linarith only [h3020, h3040, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3042 | h3042
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3043 | h3043
                  · linarith only [h1448, h3020, h3043, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2972, h3043, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3046 | h3046
                  · linarith only [h0, h2972, h3020, h3046, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2972, h3046, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1448 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1632 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1864 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1866 | h1866
  · exact r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x1_x1_x0 m hb1 hb3 hb5 h0 h1448 h1632 h1864 h1866
  · exact r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x1_x1_x1 m hb1 hb3 hb5 h0 h1448 h1632 h1864 h1866

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1448 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1632 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1864 | h1864
  · exact r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x1_x0 m hb1 hb3 hb5 h0 h1448 h1632 h1864
  · exact r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x1_x1 m hb1 hb3 hb5 h0 h1448 h1632 h1864

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1448 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1632 | h1632
  · exact r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x0 m hb1 hb3 hb5 h0 h1448 h1632
  · exact r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x1 m hb1 hb3 hb5 h0 h1448 h1632

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1448 | h1448
  · exact r1l7_11_13_25_L_I_L_I_H_R_x1_x0 m hb1 hb3 hb5 h0 h1448
  · exact r1l7_11_13_25_L_I_L_I_H_R_x1_x1 m hb1 hb3 hb5 h0 h1448

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_I_L_I_H_R_x0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_I_L_I_H_R_x1 m hb1 hb3 hb5 h0

end R2N4
