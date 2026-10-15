import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_37S7
import Jsp000404.R1LeavesN7_37S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1695 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2185 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2738 | h2738
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2739 | h2739
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2740 | h2740
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2741 | h2741
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2742 | h2742
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2743 | h2743
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2744 | h2744
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2745 | h2745
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2746 | h2746
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2747 | h2747
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2748 | h2748
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2749 | h2749
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2750 | h2750
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2751 | h2751
                            · rcases h2bigk with h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h0, hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2748, h2751, hc02, hc45, hlam, hphi, ht0b, ht5b, p2752_1]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                rcases p2752_3 (m.d 0 2) (by simp) with h2756 | h2756
                                · rcases p2752_3 (m.d 1 2) (by simp) with h2757 | h2757
                                  · rcases p2752_3 (m.d 2 3) (by simp) with h2758 | h2758
                                    · linarith only [h2738, h2758, hlam]
                                    · linarith only [h2748, h2758, hlam]
                                  · linarith only [h2744, h2757, hlam]
                                · linarith only [h2756, hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                rcases p2752_3 (m.d 0 2) (by simp) with h2763 | h2763
                                · rcases p2752_3 (m.d 1 2) (by simp) with h2764 | h2764
                                  · rcases p2752_3 (m.d 2 3) (by simp) with h2765 | h2765
                                    · linarith only [h2738, h2765, hlam]
                                    · linarith only [h2749, h2765, hlam]
                                  · linarith only [h0, h2738, h2748, h2750, h2751, h2764, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                                · linarith only [h2763, hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2738, h2748, h2751, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2752_1]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2748, h2751, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2752_1]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                rcases p2752_3 (m.d 0 2) (by simp) with h2773 | h2773
                                · linarith only [h0, h2773, hlam]
                                · linarith only [h2739, h2773, hlam]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                rcases p2752_3 (m.d 0 2) (by simp) with h2776 | h2776
                                · linarith only [h0, h2776, hlam]
                                · linarith only [h2740, h2776, hlam]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2738, hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2743, hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2738, h2748, h2751, hc02, hc45, hlam, hphi, ht0b, ht5b, p2752_1]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                rcases p2752_3 (m.d 0 2) (by simp) with h2783 | h2783
                                · rcases p2752_3 (m.d 1 2) (by simp) with h2784 | h2784
                                  · rcases p2752_3 (m.d 2 3) (by simp) with h2785 | h2785
                                    · rcases p2752_3 (m.d 2 4) (by simp) with h2786 | h2786
                                      · linarith only [h2748, h2786, hlam]
                                      · linarith only [h2750, h2786, hlam]
                                    · linarith only [h2749, h2785, hlam]
                                  · linarith only [h0, h2738, h2784, hlam, p2752_1]
                                · linarith only [h2740, h2783, hlam]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2739, hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2744, hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2748, hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                rcases p2752_3 (m.d 0 2) (by simp) with h2796 | h2796
                                · rcases p2752_3 (m.d 1 2) (by simp) with h2797 | h2797
                                  · rcases p2752_3 (m.d 2 3) (by simp) with h2798 | h2798
                                    · rcases p2752_3 (m.d 2 4) (by simp) with h2799 | h2799
                                      · rcases p2752_3 (m.d 2 5) (by simp) with h2800 | h2800
                                        · linarith only [h2750, h2800, hlam]
                                        · rcases h4bigk with h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c | h2802c
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2185, hlam, p2802_1]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2185, hc24, hlam, hphi, p2802_1, u4elo1]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2185, h2751, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2802_1, u4elo1]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            rcases p2802_3 (m.d 0 4) (by simp) with h2807 | h2807
                                            · rcases p2802_3 (m.d 1 4) (by simp) with h2808 | h2808
                                              · rcases p2802_3 (m.d 2 4) (by simp) with h2809 | h2809
                                                · linarith only [h2739, h2809, hlam]
                                                · linarith only [h2750, h2809, hlam]
                                              · linarith only [h2747, h2808, hlam]
                                            · linarith only [h2807, hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2802_1, u4elo1]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2749, h2751, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2752_1, p2802_1, u4elo1]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2751, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2802_1, u4elo1]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            rcases p2802_3 (m.d 0 4) (by simp) with h2818 | h2818
                                            · linarith only [h2185, h2818, hlam]
                                            · linarith only [h2742, h2818, hlam]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2739, hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2744, hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2739, h2751, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2802_1, u4elo0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            rcases p2802_3 (m.d 0 4) (by simp) with h2825 | h2825
                                            · rcases p2802_3 (m.d 1 4) (by simp) with h2826 | h2826
                                              · rcases p2802_3 (m.d 2 4) (by simp) with h2827 | h2827
                                                · rcases p2802_3 (m.d 3 4) (by simp) with h2828 | h2828
                                                  · linarith only [h2748, h2828, hlam]
                                                  · linarith only [h2751, h2828, hlam]
                                                · linarith only [h2827, hlam, p2802_0]
                                              · linarith only [h2747, h2826, hlam]
                                            · linarith only [h2742, h2825, hlam]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2741, hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2745, hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2748, hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h0, h2738, h2748, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2802_1]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2742, hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2747, hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2750, hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [h2751, hlam, p2802_0]
                                          · have p2802_0 := h2802c.1
                                            have p2802_1 := h2802c.2.1
                                            have p2802_2 := h2802c.2.2.1
                                            have p2802_3 := h2802c.2.2.2
                                            linarith only [hlam, p2802_0]
                                      · linarith only [h2750, h2799, hlam]
                                    · linarith only [h2749, h2798, hlam]
                                  · linarith only [h0, h2740, h2797, hlam]
                                · linarith only [h2740, h2796, hlam]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2740, hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h0, h2185, h2740, h2742, hc02, hlam, hphi, ht23, ht34, p2752_1, u4elo1]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2749, hlam, p2752_0]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [h2750, hlam, p2752_1]
                              · have p2752_0 := h2752c.1
                                have p2752_1 := h2752c.2.1
                                have p2752_2 := h2752c.2.2.1
                                have p2752_3 := h2752c.2.2.2
                                linarith only [hlam, p2752_0]
                            · linarith only [h2185, h2742, h2751, hc34, hlam, hphi, u4elo1]
                          · linarith only [h2185, h2742, h2750, hc24, hlam, hphi, u4elo1]
                        · linarith only [h2746, h2747, h2748, h2749, hc34, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2856 | h2856
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2857 | h2857
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2858 | h2858
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
                                linarith only [h0, hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                rcases p2859_3 (m.d 0 2) (by simp) with h2862 | h2862
                                · rcases p2859_3 (m.d 1 2) (by simp) with h2863 | h2863
                                  · rcases p2859_3 (m.d 2 3) (by simp) with h2864 | h2864
                                    · linarith only [h2864, hlam, p2859_0]
                                    · rcases p2859_3 (m.d 2 4) (by simp) with h2866 | h2866
                                      · linarith only [h2739, h2866, hlam]
                                      · linarith only [h2748, h2866, hlam]
                                  · linarith only [h2743, h2863, hlam]
                                · linarith only [h2862, hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                rcases p2859_3 (m.d 0 2) (by simp) with h2871 | h2871
                                · rcases p2859_3 (m.d 1 2) (by simp) with h2872 | h2872
                                  · rcases p2859_3 (m.d 2 3) (by simp) with h2873 | h2873
                                    · linarith only [h2738, h2873, hlam]
                                    · rcases p2859_3 (m.d 2 4) (by simp) with h2875 | h2875
                                      · linarith only [h2875, hlam, p2859_0]
                                      · rcases p2859_3 (m.d 2 5) (by simp) with h2877 | h2877
                                        · linarith only [h2740, h2877, hlam]
                                        · rcases h4bigk with h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c | h2879c
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2185, hlam, p2879_1]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2185, h2748, h2856, h2858, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2879_1, u4elo1]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2185, h2748, h2856, h2858, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2879_1, u4elo1]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            rcases p2879_3 (m.d 0 4) (by simp) with h2884 | h2884
                                            · rcases p2879_3 (m.d 1 4) (by simp) with h2885 | h2885
                                              · rcases p2879_3 (m.d 2 4) (by simp) with h2886 | h2886
                                                · linarith only [h2739, h2886, hlam]
                                                · linarith only [h2857, h2886, hlam]
                                              · linarith only [h2747, h2885, hlam]
                                            · linarith only [h2884, hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2879_1, u4elo1]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2748, h2856, h2858, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2879_1, u4elo1]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2748, h2856, h2858, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2879_1, u4elo1]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            rcases p2879_3 (m.d 0 4) (by simp) with h2895 | h2895
                                            · linarith only [h2185, h2895, hlam]
                                            · linarith only [h2742, h2895, hlam]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2739, hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2744, hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2748, hlam, p2879_1]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2859_1, p2879_1]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2741, hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2745, hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2741, hc24, hlam, hphi, p2879_1, u4elo0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            rcases p2879_3 (m.d 0 4) (by simp) with h2907 | h2907
                                            · rcases p2879_3 (m.d 1 4) (by simp) with h2908 | h2908
                                              · rcases p2879_3 (m.d 2 4) (by simp) with h2909 | h2909
                                                · linarith only [h2748, h2909, hlam]
                                                · linarith only [h2857, h2909, hlam]
                                              · linarith only [h2747, h2908, hlam]
                                            · linarith only [h2742, h2907, hlam]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2742, hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2747, hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2857, hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [h2858, hlam, p2879_0]
                                          · have p2879_0 := h2879c.1
                                            have p2879_1 := h2879c.2.1
                                            have p2879_2 := h2879c.2.2.1
                                            have p2879_3 := h2879c.2.2.2
                                            linarith only [hlam, p2879_0]
                                  · linarith only [h2744, h2872, hlam]
                                · linarith only [h2871, hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                rcases p2859_3 (m.d 0 2) (by simp) with h2921 | h2921
                                · rcases p2859_3 (m.d 1 2) (by simp) with h2922 | h2922
                                  · rcases p2859_3 (m.d 2 3) (by simp) with h2923 | h2923
                                    · linarith only [h2738, h2923, hlam]
                                    · linarith only [h2856, h2923, hlam]
                                  · linarith only [h0, h2185, h2741, h2748, h2856, h2922, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                                · linarith only [h2921, hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [h2738, h2856, h2858, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2859_1]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                rcases p2859_3 (m.d 0 2) (by simp) with h2930 | h2930
                                · linarith only [h0, h2930, hlam]
                                · linarith only [h2738, h2930, hlam]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                rcases p2859_3 (m.d 0 2) (by simp) with h2933 | h2933
                                · linarith only [h0, h2933, hlam]
                                · linarith only [h2739, h2933, hlam]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                rcases p2859_3 (m.d 0 2) (by simp) with h2936 | h2936
                                · linarith only [h0, h2936, hlam]
                                · linarith only [h2740, h2936, hlam]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [h2738, hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [h2743, hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [h2748, hlam, p2859_1]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [h2185, h2741, h2748, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2859_1, u4elo1]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [h2739, hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [h2744, hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, p2859_1, u4elo2]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                rcases p2859_3 (m.d 0 2) (by simp) with h2948 | h2948
                                · rcases p2859_3 (m.d 1 2) (by simp) with h2949 | h2949
                                  · rcases p2859_3 (m.d 2 3) (by simp) with h2950 | h2950
                                    · linarith only [h2748, h2950, hlam]
                                    · linarith only [h2856, h2950, hlam]
                                  · linarith only [h0, h2740, h2949, hlam]
                                · linarith only [h2740, h2948, hlam]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [h2740, hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [h0, h2856, hc01, hc23, hlam, hphi, ht12, p2859_1]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [h2856, hlam, p2859_0]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [h2857, hlam, p2859_1]
                              · have p2859_0 := h2859c.1
                                have p2859_1 := h2859c.2.1
                                have p2859_2 := h2859c.2.2.1
                                have p2859_3 := h2859c.2.2.2
                                linarith only [hlam, p2859_0]
                            · linarith only [h2185, h2742, h2748, h2858, hc24, hlam, hphi, u4elo1]
                          · linarith only [h2185, h2742, h2748, h2856, h2857, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2962 | h2962
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2963 | h2963
                            · rcases h2bigk with h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h0, hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                rcases p2964_3 (m.d 0 2) (by simp) with h2967 | h2967
                                · rcases p2964_3 (m.d 1 2) (by simp) with h2968 | h2968
                                  · rcases p2964_3 (m.d 2 3) (by simp) with h2969 | h2969
                                    · linarith only [h2969, hlam, p2964_0]
                                    · rcases p2964_3 (m.d 2 4) (by simp) with h2971 | h2971
                                      · linarith only [h2739, h2971, hlam]
                                      · linarith only [h2748, h2971, hlam]
                                  · linarith only [h2743, h2968, hlam]
                                · linarith only [h2967, hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                rcases p2964_3 (m.d 0 2) (by simp) with h2976 | h2976
                                · rcases p2964_3 (m.d 1 2) (by simp) with h2977 | h2977
                                  · rcases p2964_3 (m.d 2 3) (by simp) with h2978 | h2978
                                    · linarith only [h2738, h2978, hlam]
                                    · rcases p2964_3 (m.d 2 4) (by simp) with h2980 | h2980
                                      · linarith only [h2980, hlam, p2964_0]
                                      · rcases p2964_3 (m.d 2 5) (by simp) with h2982 | h2982
                                        · linarith only [h2740, h2982, hlam]
                                        · rcases h4bigk with h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c | h2984c
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2185, hlam, p2984_1]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2185, h2856, h2962, hc23, hlam, hphi, ht34, p2984_1, u4elo1]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2185, h2856, h2963, hc23, hlam, hphi, ht34, p2984_1, u4elo1]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            rcases p2984_3 (m.d 0 4) (by simp) with h2989 | h2989
                                            · rcases p2984_3 (m.d 1 4) (by simp) with h2990 | h2990
                                              · rcases p2984_3 (m.d 2 4) (by simp) with h2991 | h2991
                                                · linarith only [h2739, h2991, hlam]
                                                · linarith only [h2962, h2991, hlam]
                                              · linarith only [h2747, h2990, hlam]
                                            · linarith only [h2989, hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [hc04, hlam, hphi, p2984_1, u4elo1]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2962, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2984_1, u4elo1]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2856, h2963, hc23, hlam, hphi, ht34, p2984_1, u4elo1]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            rcases p2984_3 (m.d 0 4) (by simp) with h3000 | h3000
                                            · linarith only [h2185, h3000, hlam]
                                            · linarith only [h2742, h3000, hlam]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2739, hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2744, hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2748, hlam, p2984_1]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [hc02, hc45, hlam, hphi, ht0b, ht5b, p2964_1, p2984_1]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2741, hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2745, hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2741, hc24, hlam, hphi, p2984_1, u4elo0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            rcases p2984_3 (m.d 0 4) (by simp) with h3012 | h3012
                                            · rcases p2984_3 (m.d 1 4) (by simp) with h3013 | h3013
                                              · rcases p2984_3 (m.d 2 4) (by simp) with h3014 | h3014
                                                · linarith only [h2748, h3014, hlam]
                                                · linarith only [h2962, h3014, hlam]
                                              · linarith only [h2747, h3013, hlam]
                                            · linarith only [h2742, h3012, hlam]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2742, hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2747, hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2962, hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [h2963, hlam, p2984_0]
                                          · have p2984_0 := h2984c.1
                                            have p2984_1 := h2984c.2.1
                                            have p2984_2 := h2984c.2.2.1
                                            have p2984_3 := h2984c.2.2.2
                                            linarith only [hlam, p2984_0]
                                  · linarith only [h2744, h2977, hlam]
                                · linarith only [h2976, hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                rcases p2964_3 (m.d 0 2) (by simp) with h3026 | h3026
                                · rcases p2964_3 (m.d 1 2) (by simp) with h3027 | h3027
                                  · rcases p2964_3 (m.d 2 3) (by simp) with h3028 | h3028
                                    · linarith only [h2738, h3028, hlam]
                                    · rcases p2964_3 (m.d 2 4) (by simp) with h3030 | h3030
                                      · linarith only [h2739, h3030, hlam]
                                      · linarith only [h2962, h3030, hlam]
                                  · linarith only [h0, h3027, hlam, p2964_1]
                                · linarith only [h3026, hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h2739, h2962, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2964_1]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                rcases p2964_3 (m.d 0 2) (by simp) with h3037 | h3037
                                · linarith only [h0, h3037, hlam]
                                · linarith only [h2738, h3037, hlam]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                rcases p2964_3 (m.d 0 2) (by simp) with h3040 | h3040
                                · linarith only [h0, h3040, hlam]
                                · linarith only [h2739, h3040, hlam]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                rcases p2964_3 (m.d 0 2) (by simp) with h3043 | h3043
                                · linarith only [h0, h3043, hlam]
                                · linarith only [h2740, h3043, hlam]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h2738, hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h2743, hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h2748, hlam, p2964_1]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h2856, hlam, p2964_1]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h2739, hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h2744, hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, p2964_1, u4elo2]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h2741, h2748, h2856, hc23, hlam, hphi, ht34, p2964_1, u4elo0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h2740, hlam, p2964_0]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2964_1]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h2185, h2740, h2742, hc23, hlam, hphi, ht34, p2964_1, u4elo1]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [h2962, hlam, p2964_1]
                              · have p2964_0 := h2964c.1
                                have p2964_1 := h2964c.2.1
                                have p2964_2 := h2964c.2.2.1
                                have p2964_3 := h2964c.2.2.2
                                linarith only [hlam, p2964_0]
                            · linarith only [h2742, h2748, h2963, hc24, hlam, hphi, u4elo0]
                          · linarith only [h2185, h2742, h2748, h2962, hc23, hlam, hphi, ht34, u4elo1]
                    · linarith only [h2185, h2742, h2747, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3064 | h3064
                    · linarith only [h2745, h2746, h3064, hlam]
                    · linarith only [h2742, h3064, hc14, hlam, hphi, u4elo0]
                · linarith only [h1695, h2741, h2745, hlam]
              · linarith only [h0, h2744, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h2738, h2743, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3070 | h3070
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3071 | h3071
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3072 | h3072
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3073 | h3073
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3074 | h3074
                    · linarith only [h2742, h3074, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2185, h3074, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3077 | h3077
                    · linarith only [h2185, h2742, h3077, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h2185, h3077, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1695, h2741, h3072, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
              · linarith only [h0, h2739, h3071, hlam]
            · linarith only [h0, h2738, h3070, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3083 | h3083
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3084 | h3084
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3085 | h3085
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3086 | h3086
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3087 | h3087
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3088 | h3088
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3089 | h3089
                      · linarith only [h0, h1695, h2738, h2741, h3089, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3091 | h3091
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3092 | h3092
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3093 | h3093
                            · rcases h2bigk with h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h0, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                rcases p3094_3 (m.d 0 2) (by simp) with h3097 | h3097
                                · rcases p3094_3 (m.d 1 2) (by simp) with h3098 | h3098
                                  · rcases p3094_3 (m.d 2 3) (by simp) with h3099 | h3099
                                    · linarith only [h3099, hlam, p3094_0]
                                    · rcases p3094_3 (m.d 2 4) (by simp) with h3101 | h3101
                                      · linarith only [h2739, h3101, hlam]
                                      · linarith only [h3089, h3101, hlam]
                                  · linarith only [h3084, h3098, hlam]
                                · linarith only [h3097, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                rcases p3094_3 (m.d 0 2) (by simp) with h3106 | h3106
                                · rcases p3094_3 (m.d 1 2) (by simp) with h3107 | h3107
                                  · rcases p3094_3 (m.d 2 3) (by simp) with h3108 | h3108
                                    · linarith only [h2738, h3108, hlam]
                                    · rcases p3094_3 (m.d 2 4) (by simp) with h3110 | h3110
                                      · linarith only [h3110, hlam, p3094_0]
                                      · rcases p3094_3 (m.d 2 5) (by simp) with h3112 | h3112
                                        · linarith only [h2740, h3112, hlam]
                                        · rcases h4bigk with h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c | h3114c
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h2185, hlam, p3114_1]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [hc24, hlam, hphi, p3114_1, u4elo0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h2741, hlam, p3114_1]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            rcases p3114_3 (m.d 0 4) (by simp) with h3119 | h3119
                                            · rcases p3114_3 (m.d 1 4) (by simp) with h3120 | h3120
                                              · rcases p3114_3 (m.d 2 4) (by simp) with h3121 | h3121
                                                · linarith only [h2739, h3121, hlam]
                                                · linarith only [h3092, h3121, hlam]
                                              · linarith only [h3088, h3120, hlam]
                                            · linarith only [h3119, hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [hc04, hlam, hphi, p3114_1, u4elo1]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h3089, h3091, h3093, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3114_1, u4elo1]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h2741, hc03, hlam, hphi, ht34, p3114_1, u4elo1]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            rcases p3114_3 (m.d 0 4) (by simp) with h3130 | h3130
                                            · linarith only [h2185, h3130, hlam]
                                            · linarith only [h3083, h3130, hlam]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h2739, hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h3085, hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h3089, hlam, p3114_1]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3094_1, p3114_1]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [hc04, hlam, hphi, p3114_1, u4elo3]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h3086, hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h3086, hc24, hlam, hphi, p3114_1, u4elo1]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            rcases p3114_3 (m.d 0 4) (by simp) with h3142 | h3142
                                            · linarith only [h2741, h3142, hlam]
                                            · linarith only [h3083, h3142, hlam]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h3083, hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h3088, hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h3092, hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [h3093, hlam, p3114_0]
                                          · have p3114_0 := h3114c.1
                                            have p3114_1 := h3114c.2.1
                                            have p3114_2 := h3114c.2.2.1
                                            have p3114_3 := h3114c.2.2.2
                                            linarith only [hlam, p3114_0]
                                  · linarith only [h3085, h3107, hlam]
                                · linarith only [h3106, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                rcases p3094_3 (m.d 0 2) (by simp) with h3152 | h3152
                                · rcases p3094_3 (m.d 1 2) (by simp) with h3153 | h3153
                                  · rcases p3094_3 (m.d 2 3) (by simp) with h3154 | h3154
                                    · linarith only [h2738, h3154, hlam]
                                    · linarith only [h3091, h3154, hlam]
                                  · linarith only [h1695, h2738, h3084, h3091, h3153, hlam]
                                · linarith only [h3152, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h2738, h3091, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                rcases p3094_3 (m.d 0 2) (by simp) with h3161 | h3161
                                · linarith only [h0, h3161, hlam]
                                · linarith only [h2738, h3161, hlam]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                rcases p3094_3 (m.d 0 2) (by simp) with h3164 | h3164
                                · linarith only [h0, h3164, hlam]
                                · linarith only [h2739, h3164, hlam]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                rcases p3094_3 (m.d 0 2) (by simp) with h3167 | h3167
                                · linarith only [h0, h3167, hlam]
                                · linarith only [h2740, h3167, hlam]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h2738, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h3084, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h3089, hlam, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h2738, h2741, h3086, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3094_1, u4elo1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h2739, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h3085, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h2739, h3091, hc02, hc35, hlam, hphi, ht0b, ht5b, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                rcases p3094_3 (m.d 0 2) (by simp) with h3179 | h3179
                                · rcases p3094_3 (m.d 1 2) (by simp) with h3180 | h3180
                                  · rcases p3094_3 (m.d 2 3) (by simp) with h3181 | h3181
                                    · linarith only [h3089, h3181, hlam]
                                    · linarith only [h3091, h3181, hlam]
                                  · linarith only [h0, h2739, h2741, h3086, h3180, hc02, hlam, hphi, ht23, ht34, p3094_1, u4elo1]
                                · linarith only [h2740, h3179, hlam]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h2740, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h2741, h3084, h3086, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h3091, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h3092, hlam, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [hlam, p3094_0]
                            · linarith only [h2738, h2741, h3091, h3092, h3093, hlam]
                          · linarith only [h2741, h3083, h3086, h3092, hc24, hlam, hphi, u4elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3193 | h3193
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3194 | h3194
                            · rcases h2bigk with h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c | h3195c
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h0, hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                rcases p3195_3 (m.d 0 2) (by simp) with h3198 | h3198
                                · rcases p3195_3 (m.d 1 2) (by simp) with h3199 | h3199
                                  · rcases p3195_3 (m.d 2 3) (by simp) with h3200 | h3200
                                    · linarith only [h3200, hlam, p3195_0]
                                    · rcases p3195_3 (m.d 2 4) (by simp) with h3202 | h3202
                                      · linarith only [h2739, h3202, hlam]
                                      · linarith only [h3089, h3202, hlam]
                                  · linarith only [h3084, h3199, hlam]
                                · linarith only [h3198, hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                rcases p3195_3 (m.d 0 2) (by simp) with h3207 | h3207
                                · rcases p3195_3 (m.d 1 2) (by simp) with h3208 | h3208
                                  · rcases p3195_3 (m.d 2 3) (by simp) with h3209 | h3209
                                    · linarith only [h2738, h3209, hlam]
                                    · rcases p3195_3 (m.d 2 4) (by simp) with h3211 | h3211
                                      · linarith only [h3211, hlam, p3195_0]
                                      · rcases p3195_3 (m.d 2 5) (by simp) with h3213 | h3213
                                        · linarith only [h2740, h3213, hlam]
                                        · rcases h4bigk with h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c | h3215c
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h2185, hlam, p3215_1]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h2741, h3086, h3091, h3193, hc23, hlam, hphi, ht34, p3215_1, u4elo1]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h2741, hlam, p3215_1]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            rcases p3215_3 (m.d 0 4) (by simp) with h3220 | h3220
                                            · rcases p3215_3 (m.d 1 4) (by simp) with h3221 | h3221
                                              · rcases p3215_3 (m.d 2 4) (by simp) with h3222 | h3222
                                                · linarith only [h2739, h3222, hlam]
                                                · linarith only [h3193, h3222, hlam]
                                              · linarith only [h3088, h3221, hlam]
                                            · linarith only [h3220, hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [hc04, hlam, hphi, p3215_1, u4elo1]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h3193, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3215_1, u4elo1]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [hc34, hlam, hphi, p3215_1, u4elo1]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            rcases p3215_3 (m.d 0 4) (by simp) with h3231 | h3231
                                            · linarith only [h2185, h3231, hlam]
                                            · linarith only [h3083, h3231, hlam]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h2739, hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h3085, hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h3089, hlam, p3215_1]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [hc02, hc45, hlam, hphi, ht0b, ht5b, p3195_1, p3215_1]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [hc04, hlam, hphi, p3215_1, u4elo3]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h3086, hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h3086, hc24, hlam, hphi, p3215_1, u4elo1]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            rcases p3215_3 (m.d 0 4) (by simp) with h3243 | h3243
                                            · linarith only [h2741, h3243, hlam]
                                            · linarith only [h3083, h3243, hlam]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h3083, hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h3088, hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h3193, hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [h3194, hlam, p3215_0]
                                          · have p3215_0 := h3215c.1
                                            have p3215_1 := h3215c.2.1
                                            have p3215_2 := h3215c.2.2.1
                                            have p3215_3 := h3215c.2.2.2
                                            linarith only [hlam, p3215_0]
                                  · linarith only [h3085, h3208, hlam]
                                · linarith only [h3207, hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                rcases p3195_3 (m.d 0 2) (by simp) with h3253 | h3253
                                · rcases p3195_3 (m.d 1 2) (by simp) with h3254 | h3254
                                  · rcases p3195_3 (m.d 2 3) (by simp) with h3255 | h3255
                                    · linarith only [h2738, h3255, hlam]
                                    · rcases p3195_3 (m.d 2 4) (by simp) with h3257 | h3257
                                      · linarith only [h2739, h3257, hlam]
                                      · linarith only [h3193, h3257, hlam]
                                  · linarith only [h0, h3254, hlam, p3195_1]
                                · linarith only [h3253, hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h2739, h3193, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3195_1]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                rcases p3195_3 (m.d 0 2) (by simp) with h3264 | h3264
                                · linarith only [h0, h3264, hlam]
                                · linarith only [h2738, h3264, hlam]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                rcases p3195_3 (m.d 0 2) (by simp) with h3267 | h3267
                                · linarith only [h0, h3267, hlam]
                                · linarith only [h2739, h3267, hlam]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                rcases p3195_3 (m.d 0 2) (by simp) with h3270 | h3270
                                · linarith only [h0, h3270, hlam]
                                · linarith only [h2740, h3270, hlam]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h2738, hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h3084, hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h3089, hlam, p3195_1]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h3091, hlam, p3195_1]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h2739, hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h3085, hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, p3195_1, u4elo2]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h2739, h2741, h3086, h3091, hc23, hlam, hphi, ht34, p3195_1, u4elo1]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h2740, hlam, p3195_0]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3195_1]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h2740, h2741, h3083, h3086, hc23, hlam, hphi, ht34, p3195_1, u4elo1]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [h3193, hlam, p3195_1]
                              · have p3195_0 := h3195c.1
                                have p3195_1 := h3195c.2.1
                                have p3195_2 := h3195c.2.2.1
                                have p3195_3 := h3195c.2.2.2
                                linarith only [hlam, p3195_0]
                            · linarith only [h1695, h2741, h3194, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                          · linarith only [h3083, h3193, hc24, hlam, hphi, u4elo0]
                    · linarith only [h3083, h3088, hc14, hlam, hphi, u4elo0]
                  · linarith only [h2741, h3086, h3087, hc03, hc35, hlam, hphi]
                · linarith only [h1695, h3086, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3085, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h2738, h3084, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3295 | h3295
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3296 | h3296
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3297 | h3297
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3298 | h3298
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3299 | h3299
                    · linarith only [h3083, h3299, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2185, h3299, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h1695, h2741, h3297, h3298, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h1695, h3297, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h2739, h3296, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
            · linarith only [h0, h2738, h3295, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3306 | h3306
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3307 | h3307
          · linarith only [h2739, h2740, h3307, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3309 | h3309
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3310 | h3310
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3311 | h3311
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3312 | h3312
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3313 | h3313
                    · linarith only [h3307, h3313, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2185, h3313, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3316 | h3316
                    · linarith only [h2185, h3307, h3316, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h2185, h3316, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1695, h3311, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h2739, h2740, h3310, hc12, hc25, hlam, hphi]
            · linarith only [h0, h2738, h3309, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3322 | h3322
          · linarith only [h2739, h2740, h3322, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3324 | h3324
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3325 | h3325
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3326 | h3326
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3327 | h3327
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3328 | h3328
                    · linarith only [h1695, h3306, h3322, h3328, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h2185, h3328, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h1695, h3306, h3326, h3327, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h1695, h3326, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h2739, h2740, h3325, hc12, hc25, hlam, hphi]
            · linarith only [h0, h2738, h2740, h3324, hc01, hc25, hlam, hphi, ht12]
    · linarith only [h2738, h2739, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3336 | h3336
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3337 | h3337
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3338 | h3338
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3339 | h3339
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3340 | h3340
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3341 | h3341
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3342 | h3342
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3343 | h3343
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3344 | h3344
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3345 | h3345
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3346 | h3346
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3347 | h3347
                          · linarith only [h2738, h3336, h3340, h3347, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h2738, h3336, h3339, h3340, h3347, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h2738, h3337, h3343, h3346, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h2738, h3336, h3339, h3345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h3339, h3344, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3353 | h3353
                    · linarith only [h2738, h3336, h3340, h3343, h3353, hc24, hlam, hphi, u4elo1]
                    · linarith only [h3339, h3353, hc14, hlam, hphi, u4elo0]
                · linarith only [h2738, h3336, h3338, h3340, h3342, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h2738, h3336, h3340, h3341, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3358 | h3358
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3359 | h3359
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3360 | h3360
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3361 | h3361
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3362 | h3362
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3363 | h3363
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3364 | h3364
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3365 | h3365
                            · rcases h2bigk with h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h0, hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h2738, hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h0, h3340, h3362, h3365, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3366_1]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                rcases p3366_3 (m.d 0 2) (by simp) with h3371 | h3371
                                · rcases p3366_3 (m.d 1 2) (by simp) with h3372 | h3372
                                  · rcases p3366_3 (m.d 2 3) (by simp) with h3373 | h3373
                                    · rcases p3366_3 (m.d 2 4) (by simp) with h3374 | h3374
                                      · linarith only [h3336, h3374, hlam]
                                      · linarith only [h3364, h3374, hlam]
                                    · linarith only [h3363, h3373, hlam]
                                  · linarith only [h0, h3372, hlam, p3366_1]
                                · linarith only [h3371, hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h3340, hc02, hc23, hlam, hphi, p3366_1]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h3340, hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h3340, h3362, h3365, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3366_1]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                rcases p3366_3 (m.d 0 2) (by simp) with h3384 | h3384
                                · linarith only [h0, h3384, hlam]
                                · linarith only [h3337, h3384, hlam]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h3336, h3362, h3365, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3366_1]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3366_1]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                rcases p3366_3 (m.d 0 2) (by simp) with h3390 | h3390
                                · linarith only [h2738, h3390, hlam]
                                · linarith only [h3336, h3390, hlam]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                rcases p3366_3 (m.d 0 2) (by simp) with h3393 | h3393
                                · linarith only [h2738, h3393, hlam]
                                · linarith only [h3337, h3393, hlam]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h3336, hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h3358, hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h3362, hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h2738, h3336, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3366_1]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h3337, hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3366_1]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h3363, hlam, p3366_0]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [h3364, hlam, p3366_1]
                              · have p3366_0 := h3366c.1
                                have p3366_1 := h3366c.2.1
                                have p3366_2 := h3366c.2.2.1
                                have p3366_3 := h3366c.2.2.2
                                linarith only [hlam, p3366_0]
                            · linarith only [h3336, h3364, h3365, hc34, hlam, hphi, u4elo0]
                          · linarith only [h2185, h3339, h3364, hc24, hlam, hphi, u4elo1]
                        · linarith only [h0, h3340, h3363, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h3340, h3362, hc02, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h2185, h3361, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3411 | h3411
                    · linarith only [h3340, h3358, h3360, h3411, hlam]
                    · linarith only [h1695, h2185, h2738, h3336, h3339, h3411, hc01, hc13, hlam, hphi]
                · linarith only [h1695, h2185, h3338, h3359, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
              · linarith only [h0, h3358, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3416 | h3416
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3417 | h3417
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3418 | h3418
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3419 | h3419
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3420 | h3420
                    · linarith only [h2185, h3339, h3420, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h2185, h3420, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3423 | h3423
                    · linarith only [h2185, h2738, h3336, h3339, h3416, h3419, h3423, hc01, hc24, hc35, hlam, hphi, ht12, ht23, u4elo1]
                    · linarith only [h2185, h2738, h3336, h3416, h3419, h3423, hc01, hc24, hc35, hlam, hphi, ht12, ht23, u4elo4]
                · linarith only [h2738, h3336, h3416, h3418, hc24, hlam, hphi, u4elo3]
              · linarith only [h2738, h3336, h3416, h3417, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3428 | h3428
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3429 | h3429
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3430 | h3430
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3431 | h3431
                    · linarith only [h2185, h3339, h3431, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h2185, h3431, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3434 | h3434
                    · linarith only [h2185, h3339, h3434, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h2185, h3434, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h3416, h3429, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3428, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h2738, h3336, h3338, hc24, hlam, hphi, u4elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3440 | h3440
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3441 | h3441
          · linarith only [h3336, h3337, h3441, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3443 | h3443
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3444 | h3444
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3445 | h3445
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3446 | h3446
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3447 | h3447
                    · linarith only [h3441, h3447, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2185, h3447, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3450 | h3450
                    · linarith only [h2185, h2738, h3336, h3441, h3443, h3446, h3450, hc01, hc24, hc35, hlam, hphi, ht12, ht23, u4elo1]
                    · linarith only [h2185, h2738, h3336, h3443, h3446, h3450, hc01, hc24, hc35, hlam, hphi, ht12, ht23, u4elo4]
                · linarith only [h2738, h3336, h3440, h3443, h3445, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h2738, h3336, h3443, h3444, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3455 | h3455
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3456 | h3456
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3457 | h3457
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3458 | h3458
                    · linarith only [h2185, h3441, h3443, h3455, h3458, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h2185, h3458, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3461 | h3461
                    · linarith only [h2185, h3441, h3461, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h2185, h3461, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h3440, h3443, h3456, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
              · linarith only [h0, h3336, h3337, h3455, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h2738, h3336, h3440, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3467 | h3467
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3468 | h3468
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3469 | h3469
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3470 | h3470
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3471 | h3471
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3472 | h3472
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3473 | h3473
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3474 | h3474
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3475 | h3475
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3476 | h3476
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3477 | h3477
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3478 | h3478
                            · rcases h2bigk with h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c | h3479c
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h0, hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h2738, hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3336, hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3336, h3471, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3479_1, u4elo1]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                rcases p3479_3 (m.d 0 2) (by simp) with h3485 | h3485
                                · linarith only [h0, h3485, hlam]
                                · rcases p3479_3 (m.d 1 2) (by simp) with h3487 | h3487
                                  · rcases p3479_3 (m.d 2 3) (by simp) with h3488 | h3488
                                    · linarith only [h3470, h3488, hlam]
                                    · linarith only [h2738, h3488, hlam]
                                  · linarith only [h0, h3487, hlam]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h0, h2738, hc01, hc12, hlam, hphi, p3479_1]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3336, h3467, h3476, h3478, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3479_1]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3336, h3467, h3470, h3475, hlam, p3479_2]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3467, h3470, h3476, h3478, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3479_1]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3470, hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3336, h3467, h3470, h3476, h3478, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p3479_1]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                rcases p3479_3 (m.d 0 2) (by simp) with h3500 | h3500
                                · linarith only [h2738, h3500, hlam]
                                · linarith only [h3467, h3500, hlam]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3467, h3476, h3478, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p3479_1, u4elo2]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3471, hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3475, hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                rcases p3479_3 (m.d 0 2) (by simp) with h3507 | h3507
                                · linarith only [h3336, h3507, hlam]
                                · linarith only [h3467, h3507, hlam]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3467, hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3467, h3470, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3479_1]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3476, hlam, p3479_0]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [h3477, hlam, p3479_1]
                              · have p3479_0 := h3479c.1
                                have p3479_1 := h3479c.2.1
                                have p3479_2 := h3479c.2.2.1
                                have p3479_3 := h3479c.2.2.2
                                linarith only [hlam, p3479_0]
                            · linarith only [h3336, h3469, h3471, h3478, hc34, hlam, hphi, u4elo1]
                          · linarith only [h3336, h3467, h3469, h3477, hlam]
                        · linarith only [h2738, h3467, h3470, h3473, h3476, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h2738, h3467, h3475, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h3336, h3467, h3468, h3469, h3471, h3474, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3520 | h3520
                    · linarith only [h3472, h3473, h3520, hlam]
                    · linarith only [h2185, h3520, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h2738, h3468, h3470, h3472, hlam]
              · linarith only [h0, h3471, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3525 | h3525
              · linarith only [h3336, h3467, h3470, h3525, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h3525, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · linarith only [h3336, h3467, h3469, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3529 | h3529
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3530 | h3530
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3531 | h3531
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3532 | h3532
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3533 | h3533
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3534 | h3534
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3535 | h3535
                      · linarith only [h2738, h3467, h3468, h3530, h3535, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h2738, h3467, h3535, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h3529, h3534, hc14, hlam, hphi, u4elo0]
                  · linarith only [h2738, h3467, h3468, h3532, h3533, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h1695, h3532, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3531, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3542 | h3542
              · linarith only [h3336, h3467, h3530, h3542, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h3542, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · linarith only [h2738, h3467, h3468, h3529, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3546 | h3546
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3547 | h3547
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3548 | h3548
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3549 | h3549
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3550 | h3550
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3551 | h3551
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3552 | h3552
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3553 | h3553
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3554 | h3554
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3555 | h3555
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3556 | h3556
                            · rcases h2bigk with h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c | h3557c
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h0, hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h2738, hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h3336, hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h3467, hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                rcases p3557_3 (m.d 0 2) (by simp) with h3563 | h3563
                                · linarith only [h0, h3563, hlam]
                                · rcases p3557_3 (m.d 1 2) (by simp) with h3565 | h3565
                                  · rcases p3557_3 (m.d 2 3) (by simp) with h3566 | h3566
                                    · linarith only [h3548, h3566, hlam]
                                    · linarith only [h2738, h3566, hlam]
                                  · linarith only [h0, h3565, hlam]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h0, h2738, hc01, hc12, hlam, hphi, p3557_1]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h0, h3336, hc01, hc12, hlam, hphi, p3557_1]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h0, h3467, hc01, hc12, hlam, hphi, p3557_1]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h0, h3548, hc01, hc12, hlam, hphi, p3557_1]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h3548, hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h0, h3467, h3548, h3555, hc01, hc13, hlam, hphi, p3557_1]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h0, h3467, h3548, hc01, hc12, hlam, hphi, p3557_1]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, p3557_1, u4elo2]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h3549, hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h3553, hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h0, h3467, h3549, hc01, hlam, hphi, ht12, ht23, ht34, p3557_1, u4elo1]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h0, h3548, h3554, hc01, hc12, hlam, hphi, p3557_1]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h3549, h3555, hc12, hlam, hphi, ht23, ht34, p3557_1, u4elo1]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h3554, hlam, p3557_0]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [h3555, hlam, p3557_1]
                              · have p3557_0 := h3557c.1
                                have p3557_1 := h3557c.2.1
                                have p3557_2 := h3557c.2.2.1
                                have p3557_3 := h3557c.2.2.2
                                linarith only [hlam, p3557_0]
                            · linarith only [h3547, h3556, hc34, hlam, hphi, u4elo0]
                          · linarith only [h3336, h3547, h3555, hlam]
                        · linarith only [h0, h2738, h3551, h3554, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h2738, h3553, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h3336, h3547, h3549, h3552, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3594 | h3594
                    · linarith only [h3550, h3551, h3594, hlam]
                    · linarith only [h3547, h3594, hc14, hlam, hphi, u4elo0]
                · linarith only [h1695, h2738, h3546, h3550, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3549, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3599 | h3599
              · linarith only [h3336, h3548, h3599, hc02, hc23, hlam, hphi]
              · linarith only [h0, h3599, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3602 | h3602
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3603 | h3603
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3604 | h3604
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3605 | h3605
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3606 | h3606
                    · linarith only [h3547, h3606, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2185, h3606, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3609 | h3609
                    · linarith only [h0, h3336, h3547, h3609, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h2185, h3609, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1695, h3604, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h2738, h3602, h3603, hc03, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3614 | h3614
              · linarith only [h0, h3336, h3602, h3614, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3614, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3617 | h3617
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3618 | h3618
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3619 | h3619
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3620 | h3620
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3621 | h3621
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3622 | h3622
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3623 | h3623
                      · linarith only [h0, h2738, h3546, h3618, h3623, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2738, h3620, h3623, hc01, hc13, hlam, hphi]
                    · linarith only [h2185, h3622, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h2738, h3546, h3620, h3621, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h1695, h3620, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3619, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3630 | h3630
              · linarith only [h0, h3336, h3618, h3630, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3630, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3633 | h3633
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3634 | h3634
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3635 | h3635
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3636 | h3636
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3637 | h3637
                    · linarith only [h3617, h3637, hc04, hlam, hphi, u4elo1]
                    · linarith only [h2185, h3637, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h2738, h3546, h3635, h3636, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h1695, h3635, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h3634, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3643 | h3643
              · linarith only [h0, h3336, h3633, h3643, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3643, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1695 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2185 | h2185
  · exact r1l7_12_24_L_I_M_LI_x1_x1_x0 m hb2 hb4 h0 h1695 h2185
  · exact r1l7_12_24_L_I_M_LI_x1_x1_x1 m hb2 hb4 h0 h1695 h2185

set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1695 | h1695
  · exact r1l7_12_24_L_I_M_LI_x1_x0 m hb2 hb4 h0 h1695
  · exact r1l7_12_24_L_I_M_LI_x1_x1 m hb2 hb4 h0 h1695

set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_12_24_L_I_M_LI_x0 m hb2 hb4 h0
  · exact r1l7_12_24_L_I_M_LI_x1 m hb2 hb4 h0

end R2N4
