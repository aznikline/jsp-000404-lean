import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_38S8
import Jsp000404.R1LeavesN7_38S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1917 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2259 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2686 | h2686
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2687 | h2687
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2688 | h2688
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2689 | h2689
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2690 | h2690
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2691 | h2691
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2692 | h2692
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2693 | h2693
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2694 | h2694
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2695 | h2695
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2696 | h2696
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2697 | h2697
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2698 | h2698
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2699 | h2699
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2700 | h2700
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2701 | h2701
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2702 | h2702
                                  · rcases h0bigk with h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c | h2703c
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
                                      linarith only [h1917, hlam, p2703_0]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2259, hlam, p2703_1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2259, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2703_1, u4elo1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p2703_1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [hlam, p2703_0]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h0, h2687, h2699, h2702, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2703_1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h0, h2259, h2686, h2695, h2700, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2703_1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      rcases p2703_3 (m.d 0 1) (by simp) with h2713 | h2713
                                      · linarith only [h0, h2713, hlam]
                                      · linarith only [h2686, h2713, hlam]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2686, h2695, h2700, h2702, hc03, hc45, hlam, hphi, ht0b, ht5b, p2703_1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2687, hlam, p2703_1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [hlam, p2703_0]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h0, h2259, h2686, h2687, h2695, h2700, h2702, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2703_1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      rcases p2703_3 (m.d 0 1) (by simp) with h2720 | h2720
                                      · linarith only [h1917, h2720, hlam]
                                      · linarith only [h2686, h2720, hlam]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2686, h2695, h2700, h2702, hc04, hc45, hlam, hphi, ht0b, ht5b, p2703_1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2688, hlam, p2703_0]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2690, hlam, p2703_0]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [hlam, p2703_0]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2259, h2686, h2695, h2700, h2702, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2703_1, u4elo1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2686, hlam, p2703_0]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2689, hlam, p2703_1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2691, hlam, p2703_0]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [h2692, hlam, p2703_1]
                                    · have p2703_0 := h2703c.1
                                      have p2703_1 := h2703c.2.1
                                      have p2703_2 := h2703c.2.2.1
                                      have p2703_3 := h2703c.2.2.2
                                      linarith only [hlam, p2703_0]
                                  · linarith only [h2259, h2692, h2702, hc34, hlam, hphi, u4elo1]
                                · linarith only [h2259, h2686, h2698, h2701, hc24, hlam, hphi, u4elo1]
                              · linarith only [h2259, h2686, h2697, h2700, hc23, hlam, hphi, ht34, u4elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2736 | h2736
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2737 | h2737
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2738 | h2738
                                  · rcases h0bigk with h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c | h2739c
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [hlam, p2739_0]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h0, hlam, p2739_1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h1917, hlam, p2739_0]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h2259, hlam, p2739_1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2739_1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p2739_1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [hlam, p2739_0]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h0, h1917, hc01, hc12, hlam, hphi, p2739_1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h0, h2690, h2699, h2736, h2738, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2739_1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      rcases p2739_3 (m.d 0 1) (by simp) with h2749 | h2749
                                      · linarith only [h0, h2749, hlam]
                                      · linarith only [h2686, h2749, hlam]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h2686, h2695, h2736, h2738, hc03, hc45, hlam, hphi, ht0b, ht5b, p2739_1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h2687, hlam, p2739_1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [hlam, p2739_0]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h1917, h2690, h2693, h2699, h2736, h2738, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2739_1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      rcases p2739_3 (m.d 0 1) (by simp) with h2756 | h2756
                                      · linarith only [h1917, h2756, hlam]
                                      · linarith only [h2686, h2756, hlam]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h2259, h2686, h2695, h2736, h2738, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2739_1, u4elo1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h2688, hlam, p2739_0]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h2690, hlam, p2739_0]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [hlam, p2739_0]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h2259, h2686, h2695, h2736, h2738, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2739_1, u4elo1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h2686, hlam, p2739_0]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h2689, hlam, p2739_1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h2691, hlam, p2739_0]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [h2692, hlam, p2739_1]
                                    · have p2739_0 := h2739c.1
                                      have p2739_1 := h2739c.2.1
                                      have p2739_2 := h2739c.2.2.1
                                      have p2739_3 := h2739c.2.2.2
                                      linarith only [hlam, p2739_0]
                                  · linarith only [h2699, h2738, hc23, hlam, hphi, ht34, u4elo4]
                                · linarith only [h0, h2686, h2698, h2699, h2736, h2737, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h2259, h2686, h2691, h2736, hc23, hlam, hphi, ht34, u4elo1]
                          · linarith only [h2259, h2698, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1917, h2691, h2697, hlam]
                      · linarith only [h1917, h2690, h2696, hlam]
                    · linarith only [h0, h2689, h2695, hlam]
                  · linarith only [h0, h2694, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2687, h2693, hlam]
              · linarith only [h2259, h2686, h2692, hlam]
            · linarith only [h1917, h2686, h2691, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2780 | h2780
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2781 | h2781
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2782 | h2782
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2783 | h2783
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2784 | h2784
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2785 | h2785
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2786 | h2786
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2787 | h2787
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2788 | h2788
                            · linarith only [h0, h1917, h2687, h2690, h2788, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2790 | h2790
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2791 | h2791
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2792 | h2792
                                  · rcases h0bigk with h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [hlam, p2793_0]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h0, hlam, p2793_1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h1917, hlam, p2793_0]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2259, hlam, p2793_1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h1917, h2690, h2785, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p2793_1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p2793_1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [hlam, p2793_0]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h0, h1917, h2686, h2784, h2790, h2792, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2793_1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h0, h1917, h2686, h2690, h2784, h2790, h2792, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2793_1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      rcases p2793_3 (m.d 0 1) (by simp) with h2803 | h2803
                                      · linarith only [h0, h2803, hlam]
                                      · linarith only [h2686, h2803, hlam]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2686, h2690, h2784, h2785, h2790, h2792, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2793_1, u4elo1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2687, hlam, p2793_1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [hlam, p2793_0]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2690, hlam, p2793_1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2686, h2690, h2784, h2785, h2790, h2792, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2793_1, u4elo1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2686, h2784, h2790, h2792, hc04, hc45, hlam, hphi, ht0b, ht5b, p2793_1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2688, hlam, p2793_0]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2690, h2785, hc03, hlam, hphi, ht34, p2793_1, u4elo1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [hlam, p2793_0]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2686, h2690, h2784, h2785, h2790, h2792, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2793_1, u4elo1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2686, hlam, p2793_0]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2689, hlam, p2793_1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2780, hlam, p2793_0]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [h2781, hlam, p2793_1]
                                    · have p2793_0 := h2793c.1
                                      have p2793_1 := h2793c.2.1
                                      have p2793_2 := h2793c.2.2.1
                                      have p2793_3 := h2793c.2.2.2
                                      linarith only [hlam, p2793_0]
                                  · linarith only [h1917, h2686, h2690, h2784, h2792, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                                · linarith only [h1917, h2686, h2690, h2785, h2787, h2788, h2790, h2791, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h2690, h2780, h2785, h2790, hc23, hlam, hphi, ht34, u4elo1]
                          · linarith only [h1917, h2690, h2785, h2787, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1917, h2686, h2690, h2784, h2785, h2786, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1917, h2686, h2784, h2785, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h0, h2689, h2784, hlam]
                  · linarith only [h0, h2783, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2687, h2782, hlam]
              · linarith only [h1917, h2686, h2690, h2781, hlam]
            · linarith only [h1917, h2686, h2780, hlam]
        · linarith only [h0, h2686, h2689, hlam]
      · linarith only [h2687, h2688, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2834 | h2834
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2835 | h2835
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2836 | h2836
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2837 | h2837
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2838 | h2838
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2839 | h2839
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2840 | h2840
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2841 | h2841
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2842 | h2842
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2843 | h2843
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2844 | h2844
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2845 | h2845
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2846 | h2846
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2847 | h2847
                                · linarith only [h2687, h2834, h2839, h2847, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h2687, h2834, h2838, h2839, h2847, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h2686, h2687, h2837, h2841, h2846, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h2687, h2845, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h2259, h2686, h2834, h2838, h2841, h2844, hc02, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h1917, h2837, h2843, hlam]
                      · linarith only [h2687, h2834, h2836, h2838, h2839, h2842, hc03, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2259, h2686, h2687, h2834, h2839, h2841, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h2687, h2834, h2839, h2840, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2857 | h2857
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2858 | h2858
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2859 | h2859
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2860 | h2860
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2861 | h2861
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2862 | h2862
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2863 | h2863
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2864 | h2864
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2865 | h2865
                                  · rcases h0bigk with h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c | h2866c
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [hlam, p2866_0]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h0, hlam, p2866_1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h1917, hlam, p2866_0]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2259, hlam, p2866_1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2259, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2866_1, u4elo1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2686, hc02, hc15, hlam, hphi, ht0b, ht5b, p2866_1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [hlam, p2866_0]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2687, hlam, p2866_0]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h0, h2259, h2686, h2839, h2858, h2863, hc04, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2866_1, u4elo1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h0, h2686, h2839, h2858, h2863, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2866_1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h1917, h2686, h2839, h2858, h2863, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2866_1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h1917, h2839, hc02, hc23, hlam, hphi, p2866_1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [hlam, p2866_0]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h1917, h2259, h2686, h2839, h2858, h2863, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2866_1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      rcases p2866_3 (m.d 0 1) (by simp) with h2881 | h2881
                                      · linarith only [h1917, h2881, hlam]
                                      · linarith only [h2686, h2881, hlam]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2686, h2858, h2863, h2865, hc04, hc45, hlam, hphi, ht0b, ht5b, p2866_1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2834, hlam, p2866_0]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2836, hlam, p2866_0]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [hlam, p2866_0]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2686, h2858, h2863, h2865, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2866_1, u4elo0]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2686, hlam, p2866_0]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2835, hlam, p2866_1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2837, hlam, p2866_0]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [h2838, hlam, p2866_1]
                                    · have p2866_0 := h2866c.1
                                      have p2866_1 := h2866c.2.1
                                      have p2866_2 := h2866c.2.2.1
                                      have p2866_3 := h2866c.2.2.2
                                      linarith only [hlam, p2866_0]
                                  · linarith only [h2259, h2838, h2865, hc34, hlam, hphi, u4elo1]
                                · linarith only [h0, h2686, h2839, h2861, h2864, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h2259, h2686, h2839, h2860, h2863, hc02, hlam, hphi, ht23, ht34, u4elo1]
                            · linarith only [h2259, h2686, h2839, h2857, h2861, h2862, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h2259, h2686, h2860, h2861, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h1917, h2837, h2860, hlam]
                      · linarith only [h1917, h2687, h2834, h2836, h2859, hc24, hlam, hphi, u4elo0]
                    · linarith only [h2259, h2686, h2835, h2857, h2858, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h2834, h2857, hlam]
              · linarith only [h2259, h2686, h2838, hlam]
            · linarith only [h1917, h2686, h2837, hlam]
          · linarith only [h2687, h2834, h2836, hc24, hlam, hphi, u4elo3]
        · linarith only [h0, h2686, h2835, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2907 | h2907
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2908 | h2908
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2909 | h2909
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2910 | h2910
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2911 | h2911
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2912 | h2912
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2913 | h2913
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2914 | h2914
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2915 | h2915
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2916 | h2916
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2917 | h2917
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2918 | h2918
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2919 | h2919
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2920 | h2920
                                  · rcases h0bigk with h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [hlam, p2921_0]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h0, hlam, p2921_1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h1917, hlam, p2921_0]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2259, hlam, p2921_1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h0, h2834, h2912, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2921_1, u4elo1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2834, h2912, hc01, hlam, hphi, ht12, ht23, ht34, p2921_1, u4elo1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [hlam, p2921_0]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2687, hlam, p2921_0]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2834, hlam, p2921_1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2686, h2834, h2912, h2913, h2918, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2921_1, u4elo1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2686, h2913, h2918, hc03, hc35, hlam, hphi, ht0b, ht5b, p2921_1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2687, hc02, hc23, hlam, hphi, p2921_1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [hlam, p2921_0]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h0, h2686, h2834, h2913, h2918, hc03, hc35, hlam, hphi, ht0b, ht5b, p2921_1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2686, h2687, h2911, h2913, h2918, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2921_1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2686, h2913, h2918, hc04, hc35, hlam, hphi, ht0b, ht5b, p2921_1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h0, h2686, h2834, h2912, h2913, h2918, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2921_1, u4elo1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2908, hlam, p2921_0]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [hlam, p2921_0]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2686, h2834, h2912, h2913, h2918, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2921_1, u4elo1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2686, hlam, p2921_0]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2907, hlam, p2921_1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2909, hlam, p2921_0]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [h2910, hlam, p2921_1]
                                    · have p2921_0 := h2921c.1
                                      have p2921_1 := h2921c.2.1
                                      have p2921_2 := h2921c.2.2.1
                                      have p2921_3 := h2921c.2.2.2
                                      linarith only [hlam, p2921_0]
                                  · linarith only [h2834, h2910, h2912, h2920, hc34, hlam, hphi, u4elo1]
                                · linarith only [h2259, h2686, h2834, h2916, h2919, hc04, hlam, hphi, u4elo1]
                              · linarith only [h2687, h2909, h2918, hlam]
                            · linarith only [h0, h2687, h2917, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h2259, h2686, h2915, h2916, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h1917, h2686, h2909, h2915, hc03, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1917, h2686, h2913, h2914, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h2687, h2907, h2913, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h2687, h2911, h2912, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2956 | h2956
                  · linarith only [h0, h2686, h2834, h2911, h2956, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h2686, h2956, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h2259, h2686, h2910, hlam]
            · linarith only [h1917, h2686, h2909, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2961 | h2961
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2962 | h2962
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2963 | h2963
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2964 | h2964
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2965 | h2965
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2966 | h2966
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2967 | h2967
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2968 | h2968
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2969 | h2969
                            · linarith only [h0, h2687, h2908, h2963, h2969, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h2686, h2687, h2965, h2966, h2969, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                          · linarith only [h2259, h2686, h2965, h2968, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h0, h2686, h2687, h2908, h2965, h2966, h2967, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1917, h2686, h2965, h2966, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h2687, h2907, h2965, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h2687, h2963, h2964, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2977 | h2977
                  · linarith only [h0, h2686, h2834, h2963, h2977, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h2686, h2977, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h1917, h2686, h2908, h2962, hlam]
            · linarith only [h0, h2686, h2687, h2961, hlam]
        · linarith only [h0, h2686, h2907, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2983 | h2983
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2984 | h2984
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2985 | h2985
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2986 | h2986
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2987 | h2987
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2988 | h2988
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2989 | h2989
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2990 | h2990
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2991 | h2991
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2992 | h2992
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2993 | h2993
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2994 | h2994
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2995 | h2995
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2996 | h2996
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2997 | h2997
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2998 | h2998
                                  · rcases h0bigk with h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c | h2999c
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [hlam, p2999_0]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h0, hlam, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h1917, hlam, p2999_0]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h2259, hlam, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h2686, hlam, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [hlam, p2999_0]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h0, h2983, h2995, h2998, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h0, h2259, hc01, hc12, hlam, hphi, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h0, h2686, hc01, hc12, hlam, hphi, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h1917, hc01, hc13, hlam, hphi, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h2983, hlam, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [hlam, p2999_0]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h0, h2259, h2983, hc01, hc12, hlam, hphi, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h0, h2686, h2983, hc01, hc12, hlam, hphi, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p2999_1, u4elo0]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h2984, hlam, p2999_0]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h2986, hlam, p2999_0]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [hlam, p2999_0]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h2259, h2686, hc01, hlam, hphi, ht12, ht23, ht34, p2999_1, u4elo1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h2686, hc01, hc15, hlam, hphi, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h2985, hlam, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h2987, hlam, p2999_0]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [h2988, hlam, p2999_1]
                                    · have p2999_0 := h2999c.1
                                      have p2999_1 := h2999c.2.1
                                      have p2999_2 := h2999c.2.2.1
                                      have p2999_3 := h2999c.2.2.2
                                      linarith only [hlam, p2999_0]
                                  · linarith only [h2259, h2988, h2998, hc34, hlam, hphi, u4elo1]
                                · linarith only [h2259, h2988, h2997, hc24, hlam, hphi, u4elo1]
                              · linarith only [h2259, h2987, h2988, h2995, h2996, hc34, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3028 | h3028
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3029 | h3029
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3030 | h3030
                                  · rcases h0bigk with h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c | h3031c
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [hlam, p3031_0]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h0, hlam, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h1917, hlam, p3031_0]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h2259, hlam, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h2686, hlam, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [hlam, p3031_0]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h0, h1917, hc01, hc12, hlam, hphi, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h0, h2259, hc01, hc12, hlam, hphi, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h0, h2686, hc01, hc12, hlam, hphi, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h1917, h2989, hc01, hc12, hlam, hphi, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h2983, hlam, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [hlam, p3031_0]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h1917, h2984, h2989, h2995, h3028, h3030, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h1917, h2686, h2989, hc01, hc12, hlam, hphi, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p3031_1, u4elo0]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h2984, hlam, p3031_0]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h2986, hlam, p3031_0]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [hlam, p3031_0]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h2259, h2686, hc01, hlam, hphi, ht12, ht23, ht34, p3031_1, u4elo1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h2686, h2994, hc01, hlam, hphi, ht12, ht23, ht34, p3031_1, u4elo1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h2985, hlam, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h2987, hlam, p3031_0]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [h2988, hlam, p3031_1]
                                    · have p3031_0 := h3031c.1
                                      have p3031_1 := h3031c.2.1
                                      have p3031_2 := h3031c.2.2.1
                                      have p3031_3 := h3031c.2.2.2
                                      linarith only [hlam, p3031_0]
                                  · linarith only [h2995, h3028, h3030, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                                · linarith only [h2259, h2988, h3029, hc24, hlam, hphi, u4elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3059 | h3059
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3060 | h3060
                                  · rcases h0bigk with h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c | h3061c
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [hlam, p3061_0]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h0, hlam, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h1917, hlam, p3061_0]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h2259, hlam, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h2686, hlam, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [hlam, p3061_0]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h0, h1917, hc01, hc12, hlam, hphi, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h0, h2259, hc01, hc12, hlam, hphi, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h0, h2686, hc01, hc12, hlam, hphi, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h1917, h2989, hc01, hc12, hlam, hphi, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h2983, hlam, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [hlam, p3061_0]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h1917, h2984, h2989, h3059, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h1917, h2686, h2989, hc01, hc12, hlam, hphi, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p3061_1, u4elo0]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h2984, hlam, p3061_0]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h2986, hlam, p3061_0]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [hlam, p3061_0]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h2259, h2987, h3028, hc23, hlam, hphi, ht34, p3061_1, u4elo1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h2686, h2994, hc01, hlam, hphi, ht12, ht23, ht34, p3061_1, u4elo1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h2985, hlam, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h2987, hlam, p3061_0]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [h2988, hlam, p3061_1]
                                    · have p3061_0 := h3061c.1
                                      have p3061_1 := h3061c.2.1
                                      have p3061_2 := h3061c.2.2.1
                                      have p3061_3 := h3061c.2.2.2
                                      linarith only [hlam, p3061_0]
                                  · linarith only [h3059, h3060, hc34, hlam, hphi, u4elo2]
                                · linarith only [h2259, h2988, h3059, hc24, hlam, hphi, u4elo1]
                          · linarith only [h2259, h2988, h2994, hlam]
                        · linarith only [h1917, h2987, h2993, hlam]
                      · linarith only [h1917, h2986, h2992, hlam]
                    · linarith only [h0, h2985, h2991, hlam]
                  · linarith only [h0, h2990, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2983, h2989, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3095 | h3095
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3096 | h3096
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3097 | h3097
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3098 | h3098
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3099 | h3099
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3100 | h3100
                          · linarith only [h2988, h3100, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2259, h3100, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1917, h2987, h3099, hlam]
                      · linarith only [h1917, h2986, h3098, hlam]
                    · linarith only [h0, h2985, h3097, hlam]
                  · linarith only [h0, h2983, h2986, h3096, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h2983, h3095, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3108 | h3108
              · linarith only [h2986, h2987, h3108, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3110 | h3110
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3111 | h3111
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3112 | h3112
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3113 | h3113
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3114 | h3114
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3115 | h3115
                          · linarith only [h3108, h3115, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2259, h3115, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3118 | h3118
                          · linarith only [h2259, h3108, h3118, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h2259, h3118, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h1917, h3113, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2985, h3108, h3112, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h1917, h3110, h3111, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2983, h3110, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3125 | h3125
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3126 | h3126
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3127 | h3127
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3128 | h3128
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3129 | h3129
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3130 | h3130
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3131 | h3131
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3132 | h3132
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3133 | h3133
                            · linarith only [h2983, h2986, h3125, h3133, hc02, hc35, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3135 | h3135
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3136 | h3136
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3137 | h3137
                                  · rcases h0bigk with h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h0, hlam, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h1917, hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2259, hlam, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2686, hlam, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h0, h2983, h3135, h3137, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h0, h2983, h2986, h3135, h3137, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h0, h2686, hc01, hc12, hlam, hphi, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2986, h3130, hc01, hc13, hlam, hphi, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2983, hlam, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2986, hlam, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2686, h2986, h3130, hc01, hlam, hphi, ht12, ht23, ht34, p3138_1, u4elo1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p3138_1, u4elo0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2984, hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2986, h3130, hc03, hlam, hphi, ht34, p3138_1, u4elo1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2686, h2986, h3130, hc01, hlam, hphi, ht12, ht23, ht34, p3138_1, u4elo1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2686, h3132, hc01, hlam, hphi, ht12, ht23, ht34, p3138_1, u4elo1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2985, hlam, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h3125, hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h3126, hlam, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [hlam, p3138_0]
                                  · linarith only [h2986, h3137, hc03, hlam, hphi, ht34, u4elo4]
                                · linarith only [h2986, h3125, h3126, h3136, hc24, hlam, hphi, u4elo3]
                              · linarith only [h2986, h3125, h3130, h3135, hc23, hlam, hphi, ht34, u4elo1]
                          · linarith only [h2986, h3125, h3126, h3130, h3132, hlam]
                        · linarith only [h2986, h3125, h3130, h3131, hc13, hlam, hphi, ht34, u4elo1]
                      · linarith only [h1917, h3130, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2985, h2986, h3125, h3129, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h0, h3128, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2983, h3127, hlam]
              · linarith only [h2986, h3125, h3126, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3174 | h3174
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3175 | h3175
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3176 | h3176
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3177 | h3177
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3178 | h3178
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3179 | h3179
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3180 | h3180
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3181 | h3181
                            · linarith only [h0, h1917, h2983, h2986, h3181, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3183 | h3183
                              · linarith only [h2983, h3125, h3183, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3185 | h3185
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3186 | h3186
                                  · rcases h0bigk with h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c | h3187c
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [hlam, p3187_0]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h0, hlam, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h1917, hlam, p3187_0]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h2259, hlam, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h2686, hlam, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [hlam, p3187_0]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h0, h1917, hc01, hc12, hlam, hphi, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h0, h2984, h3185, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h0, h2686, hc01, hc12, hlam, hphi, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h3125, h3178, h3186, hc01, hc13, hlam, hphi, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h2983, hlam, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [hlam, p3187_0]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h2986, hlam, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h3125, hlam, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p3187_1, u4elo0]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h2984, hlam, p3187_0]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h2259, hc03, hlam, hphi, ht34, p3187_1, u4elo1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [hlam, p3187_0]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h1917, h2259, h3125, hc01, hlam, hphi, ht12, ht23, ht34, p3187_1, u4elo1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h2686, hc01, hc15, hlam, hphi, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h2985, hlam, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h1917, h3125, h3186, hc01, hlam, hphi, ht12, ht23, ht34, p3187_1, u4elo3]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [h3174, hlam, p3187_1]
                                    · have p3187_0 := h3187c.1
                                      have p3187_1 := h3187c.2.1
                                      have p3187_2 := h3187c.2.2.1
                                      have p3187_3 := h3187c.2.2.2
                                      linarith only [hlam, p3187_0]
                                  · linarith only [h2986, h3185, h3186, hc04, hlam, hphi, u4elo2]
                                · linarith only [h3174, h3185, hc24, hlam, hphi, u4elo0]
                          · linarith only [h2986, h3174, h3178, h3180, hlam]
                        · linarith only [h1917, h2986, h3178, h3179, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1917, h3178, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2985, h3177, hlam]
                  · linarith only [h1917, h3175, h3176, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2983, h3175, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3221 | h3221
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3222 | h3222
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3223 | h3223
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3224 | h3224
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3225 | h3225
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3226 | h3226
                          · linarith only [h3174, h3226, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2259, h3226, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1917, h2986, h3224, h3225, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1917, h3224, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2985, h3223, hlam]
                  · linarith only [h1917, h3221, h3222, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2983, h3221, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3234 | h3234
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3235 | h3235
            · linarith only [h2983, h2985, h3235, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3237 | h3237
              · linarith only [h2984, h2985, h3237, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3239 | h3239
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3240 | h3240
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3241 | h3241
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3242 | h3242
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3243 | h3243
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3244 | h3244
                          · linarith only [h2259, h3237, h3244, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h2259, h3244, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3247 | h3247
                          · linarith only [h2259, h3237, h3247, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h2259, h3247, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h1917, h3242, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3251 | h3251
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3252 | h3252
                        · linarith only [h3234, h3235, h3239, h3241, h3252, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3254 | h3254
                          · linarith only [h2259, h3237, h3254, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h2259, h3254, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h1917, h3251, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h3240, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2983, h3239, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3260 | h3260
            · linarith only [h2983, h2985, h3260, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3262 | h3262
              · linarith only [h2984, h2985, h3262, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3264 | h3264
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3265 | h3265
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3266 | h3266
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3267 | h3267
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3268 | h3268
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3269 | h3269
                          · linarith only [h3262, h3269, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2259, h3269, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1917, h3234, h3267, h3268, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1917, h3267, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3274 | h3274
                      · linarith only [h1917, h3234, h3264, h3266, h3274, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h1917, h3274, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h3265, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2983, h3264, hlam]
      · linarith only [h2983, h2984, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3280 | h3280
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3281 | h3281
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3282 | h3282
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3283 | h3283
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3284 | h3284
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3285 | h3285
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3286 | h3286
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3287 | h3287
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3288 | h3288
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3289 | h3289
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3290 | h3290
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3291 | h3291
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3292 | h3292
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3293 | h3293
                                · linarith only [h2983, h3280, h3285, h3293, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h2983, h3280, h3284, h3285, h3293, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h2983, h3281, h3283, h3292, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h2983, h3280, h3284, h3291, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h3284, h3290, hc14, hlam, hphi, u4elo0]
                        · linarith only [h1917, h2983, h3280, h3283, h3284, h3285, h3289, hc01, hc12, hlam, hphi]
                      · linarith only [h2983, h3280, h3282, h3285, h3288, hlam]
                    · linarith only [h2983, h3285, h3287, hc02, hc25, hlam, hphi]
                  · linarith only [h2983, h3280, h3285, h3286, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3303 | h3303
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3304 | h3304
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3305 | h3305
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3306 | h3306
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3307 | h3307
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3308 | h3308
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3309 | h3309
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3310 | h3310
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3311 | h3311
                                  · rcases h0bigk with h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [hlam, p3312_0]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h0, hlam, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h1917, hlam, p3312_0]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h2259, hlam, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h2686, hlam, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [hlam, p3312_0]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h2983, hlam, p3312_0]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h0, h3285, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h0, h2686, h3285, hc01, hc23, hlam, hphi, ht12, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h2983, hc01, hc23, hlam, hphi, ht12, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h2983, hc02, hc23, hlam, hphi, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [hlam, p3312_0]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h2983, h3280, h3308, h3311, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h2686, h2983, hc01, hc23, hlam, hphi, ht12, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p3312_1, u4elo0]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h3280, hlam, p3312_0]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h3282, hlam, p3312_0]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [hlam, p3312_0]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h2259, h2686, hc01, hlam, hphi, ht12, ht23, ht34, p3312_1, u4elo1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h2686, h3307, hc01, hlam, hphi, ht12, ht23, ht34, p3312_1, u4elo1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h3281, hlam, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h3283, hlam, p3312_0]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [h3284, hlam, p3312_1]
                                    · have p3312_0 := h3312c.1
                                      have p3312_1 := h3312c.2.1
                                      have p3312_2 := h3312c.2.2.1
                                      have p3312_3 := h3312c.2.2.2
                                      linarith only [hlam, p3312_0]
                                  · linarith only [h2259, h3284, h3311, hc34, hlam, hphi, u4elo1]
                                · linarith only [h2259, h3284, h3310, hc24, hlam, hphi, u4elo1]
                              · linarith only [h0, h3285, h3309, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h2686, h3285, h3303, h3307, h3308, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h3284, h3307, hc14, hlam, hphi, u4elo0]
                        · linarith only [h1917, h3283, h3306, hlam]
                      · linarith only [h1917, h3282, h3305, hlam]
                    · linarith only [h0, h3281, h3304, hlam]
                  · linarith only [h0, h3303, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3347 | h3347
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3348 | h3348
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3349 | h3349
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3350 | h3350
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3351 | h3351
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3352 | h3352
                          · linarith only [h3284, h3352, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2259, h3352, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h2983, h3281, h3283, h3347, h3351, hlam]
                      · linarith only [h2983, h3347, h3350, hc02, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h2983, h3281, h3349, hc12, hc23, hlam, hphi]
                  · linarith only [h2983, h3347, h3348, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3359 | h3359
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3360 | h3360
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3361 | h3361
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3362 | h3362
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3363 | h3363
                          · linarith only [h2259, h3284, h3363, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h2259, h3363, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1917, h3283, h3362, hlam]
                      · linarith only [h0, h3282, h3347, h3361, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                    · linarith only [h0, h3281, h3360, hlam]
                  · linarith only [h0, h3359, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h2983, h3281, h3283, hlam]
          · linarith only [h2983, h3280, h3282, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3372 | h3372
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3373 | h3373
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3374 | h3374
              · linarith only [h3280, h3281, h3374, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3376 | h3376
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3377 | h3377
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3378 | h3378
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3379 | h3379
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3380 | h3380
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3381 | h3381
                          · linarith only [h3374, h3381, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2259, h3381, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1917, h3373, h3380, hlam]
                      · linarith only [h1917, h3372, h3379, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                    · linarith only [h2983, h3280, h3376, h3378, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h2983, h3280, h3376, h3377, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3388 | h3388
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3389 | h3389
                    · linarith only [h3280, h3281, h3376, h3389, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3391 | h3391
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3392 | h3392
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3393 | h3393
                          · linarith only [h3374, h3393, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2259, h3393, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1917, h3373, h3392, hlam]
                      · linarith only [h0, h3376, h3391, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h3388, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3399 | h3399
              · linarith only [h2983, h3280, h3373, h3399, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3401 | h3401
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3402 | h3402
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3403 | h3403
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3404 | h3404
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3405 | h3405
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3406 | h3406
                          · linarith only [h3399, h3406, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2259, h3406, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3409 | h3409
                          · linarith only [h2259, h2983, h3280, h3399, h3401, h3405, h3409, hc01, hc24, hc35, hlam, hphi, ht12, ht23, u4elo1]
                          · linarith only [h2259, h2983, h3280, h3401, h3405, h3409, hc01, hc24, hc35, hlam, hphi, ht12, ht23, u4elo4]
                      · linarith only [h2983, h3280, h3401, h3404, hc24, hlam, hphi, u4elo3]
                    · linarith only [h2983, h3280, h3401, h3403, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h2983, h3280, h3401, h3402, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3415 | h3415
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3416 | h3416
                    · linarith only [h3280, h3281, h3401, h3416, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3418 | h3418
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3419 | h3419
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3420 | h3420
                          · linarith only [h2259, h3399, h3420, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h2259, h2983, h3280, h3373, h3401, h3419, h3420, hc01, hc23, hc24, hlam, hphi, ht12, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3423 | h3423
                          · linarith only [h2259, h3399, h3423, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h2259, h3423, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h0, h3401, h3418, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h3415, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · linarith only [h2983, h3280, h3372, hc24, hlam, hphi, u4elo3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3429 | h3429
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3430 | h3430
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3431 | h3431
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3432 | h3432
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3433 | h3433
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3434 | h3434
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3435 | h3435
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3436 | h3436
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3437 | h3437
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3438 | h3438
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3439 | h3439
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3440 | h3440
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3441 | h3441
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3442 | h3442
                                  · rcases h0bigk with h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [hlam, p3443_0]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h0, hlam, p3443_1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h1917, hlam, p3443_0]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h2259, hlam, p3443_1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h2686, hlam, p3443_1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h3280, h3434, hc01, hlam, hphi, ht12, ht23, ht34, p3443_1, u4elo1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [hlam, p3443_0]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h2983, hlam, p3443_0]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h3280, hlam, p3443_1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h3280, h3434, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3443_1, u4elo1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h1917, hc01, hc13, hlam, hphi, p3443_1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h2983, h3433, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3443_1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [hlam, p3443_0]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h2983, h3280, h3429, h3433, h3440, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3443_1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h2686, h2983, h3433, hc01, hc12, hlam, hphi, p3443_1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p3443_1, u4elo0]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h3429, h3440, hc04, hc35, hlam, hphi, ht0b, ht5b, p3443_1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h3430, hlam, p3443_0]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [hlam, p3443_0]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h2686, h3280, h3434, hc01, hlam, hphi, ht12, ht23, ht34, p3443_1, u4elo1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h2686, h3438, hc01, hlam, hphi, ht12, ht23, ht34, p3443_1, u4elo1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h3429, hlam, p3443_1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h3431, hlam, p3443_0]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [h3432, hlam, p3443_1]
                                    · have p3443_0 := h3443c.1
                                      have p3443_1 := h3443c.2.1
                                      have p3443_2 := h3443c.2.2.1
                                      have p3443_3 := h3443c.2.2.2
                                      linarith only [hlam, p3443_0]
                                  · linarith only [h3280, h3432, h3434, h3442, hc34, hlam, hphi, u4elo1]
                                · linarith only [h3280, h3429, h3432, h3441, hlam]
                              · linarith only [h2983, h3431, h3440, hlam]
                            · linarith only [h2983, h3439, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h2259, h3438, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1917, h3280, h3429, h3431, h3434, h3437, hc03, hlam, hphi, ht34, u4elo1]
                      · linarith only [h2983, h3429, h3430, h3433, h3436, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2983, h3280, h3429, h3433, h3434, h3435, hc03, hlam, hphi, ht34, u4elo1]
                  · linarith only [h2983, h3433, h3434, hc03, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3478 | h3478
                  · linarith only [h3280, h3429, h3433, h3478, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h3478, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h3280, h3429, h3432, hlam]
            · linarith only [h3280, h3429, h3430, h3431, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3483 | h3483
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3484 | h3484
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3485 | h3485
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3486 | h3486
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3487 | h3487
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3488 | h3488
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3489 | h3489
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3490 | h3490
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3491 | h3491
                            · linarith only [h2983, h3429, h3430, h3485, h3491, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h2983, h3429, h3488, h3491, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                          · linarith only [h3484, h3490, hc14, hlam, hphi, u4elo0]
                        · linarith only [h3430, h3483, h3488, h3489, hlam]
                      · linarith only [h1917, h3488, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h2983, h3429, h3487, hc12, hc23, hlam, hphi]
                  · linarith only [h2983, h3485, h3486, hc02, hlam, hphi, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3499 | h3499
                  · linarith only [h3280, h3429, h3485, h3499, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h3499, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h2983, h3429, h3430, h3484, hlam]
            · linarith only [h2983, h3429, h3483, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3504 | h3504
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3505 | h3505
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3506 | h3506
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3507 | h3507
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3508 | h3508
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3509 | h3509
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3510 | h3510
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3511 | h3511
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3512 | h3512
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3513 | h3513
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3514 | h3514
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3515 | h3515
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3516 | h3516
                                  · rcases h0bigk with h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c | h3517c
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [hlam, p3517_0]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h0, hlam, p3517_1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h1917, hlam, p3517_0]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h2259, hlam, p3517_1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h2686, hlam, p3517_1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h3429, h3509, h3510, h3512, hc01, hc13, hlam, hphi, p3517_1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [hlam, p3517_0]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h2983, hlam, p3517_0]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h3280, hlam, p3517_1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h3429, hlam, p3517_0]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h1917, hc01, hc13, hlam, hphi, p3517_1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h2983, hc02, hc23, hlam, hphi, p3517_1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [hlam, p3517_0]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h2259, h2983, hc01, hc23, hlam, hphi, ht12, p3517_1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h2686, h2983, hc01, hc23, hlam, hphi, ht12, p3517_1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p3517_1, u4elo0]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h0, h2259, hc01, hlam, hphi, ht12, ht23, ht34, p3517_1, u4elo1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h3504, hlam, p3517_0]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [hlam, p3517_0]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h0, h2259, h3429, hc01, hlam, hphi, ht12, ht23, ht34, p3517_1, u4elo1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h2686, h3512, hc01, hlam, hphi, ht12, ht23, ht34, p3517_1, u4elo1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h0, h3429, h3509, h3512, hc01, hlam, hphi, ht12, ht23, ht34, p3517_1, u4elo1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h3505, hlam, p3517_0]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [h3506, hlam, p3517_1]
                                    · have p3517_0 := h3517c.1
                                      have p3517_1 := h3517c.2.1
                                      have p3517_2 := h3517c.2.2.1
                                      have p3517_3 := h3517c.2.2.2
                                      linarith only [hlam, p3517_0]
                                  · linarith only [h3280, h3506, h3508, h3516, hc34, hlam, hphi, u4elo1]
                                · linarith only [h3280, h3506, h3515, hlam]
                              · linarith only [h2983, h3505, h3514, hlam]
                            · linarith only [h0, h2983, h3513, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h3506, h3508, h3512, hc24, hlam, hphi, u4elo0]
                        · linarith only [h1917, h2983, h3505, h3511, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h2983, h3504, h3507, h3510, hlam]
                    · linarith only [h0, h2983, h3507, h3509, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2983, h3507, h3508, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3552 | h3552
                  · linarith only [h0, h3280, h3507, h3552, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3552, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3555 | h3555
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3556 | h3556
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3557 | h3557
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3558 | h3558
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3559 | h3559
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3560 | h3560
                          · linarith only [h3506, h3560, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2259, h3560, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1917, h3429, h3505, h3557, h3559, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2983, h3555, h3558, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2983, h3555, h3557, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2983, h3555, h3556, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3567 | h3567
                  · linarith only [h0, h3280, h3555, h3567, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3567, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3570 | h3570
              · linarith only [h3504, h3505, h3570, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3572 | h3572
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3573 | h3573
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3574 | h3574
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3575 | h3575
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3576 | h3576
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3577 | h3577
                          · linarith only [h3570, h3577, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2259, h3577, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3580 | h3580
                          · linarith only [h0, h3280, h3570, h3575, h3576, h3580, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h2259, h3580, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h2983, h3504, h3572, h3575, hlam]
                    · linarith only [h0, h2983, h3572, h3574, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2983, h3572, h3573, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3586 | h3586
                  · linarith only [h0, h3280, h3572, h3586, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3586, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3589 | h3589
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3590 | h3590
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3591 | h3591
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3592 | h3592
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3593 | h3593
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3594 | h3594
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3595 | h3595
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3596 | h3596
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3597 | h3597
                            · linarith only [h0, h3429, h3504, h3589, h3591, h3597, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h2983, h3594, h3597, hc01, hc13, hlam, hphi]
                          · linarith only [h2259, h3596, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h3504, h3589, h3594, h3595, hc13, hlam, hphi, ht34, u4elo1]
                      · linarith only [h0, h2983, h3591, h3594, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2983, h3591, h3593, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2983, h3591, h3592, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3605 | h3605
                  · linarith only [h0, h3280, h3591, h3605, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3605, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h3504, h3589, h3590, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3609 | h3609
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3610 | h3610
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3611 | h3611
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3612 | h3612
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3613 | h3613
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3614 | h3614
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3615 | h3615
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3616 | h3616
                            · linarith only [h0, h2983, h3504, h3610, h3616, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h2983, h3613, h3616, hc01, hc13, hlam, hphi]
                          · linarith only [h2259, h3615, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h2983, h3504, h3613, h3614, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1917, h3613, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2983, h3610, h3612, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2983, h3610, h3611, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3624 | h3624
                  · linarith only [h0, h3280, h3610, h3624, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3624, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3627 | h3627
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3628 | h3628
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3629 | h3629
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3630 | h3630
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3631 | h3631
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3632 | h3632
                          · linarith only [h3609, h3632, hc04, hlam, hphi, u4elo1]
                          · linarith only [h2259, h3632, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h2983, h3504, h3630, h3631, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1917, h3630, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2983, h3627, h3629, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h2983, h3627, h3628, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3639 | h3639
                  · linarith only [h0, h3280, h3627, h3639, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3639, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1917 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2259 | h2259
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h1917 h2259
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h1917 h2259

set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1917 | h1917
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x1_x0 m hb0 hb1 hb3 hb4 h0 h1917
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x1_x1 m hb0 hb1 hb3 hb4 h0 h1917

end R2N4
