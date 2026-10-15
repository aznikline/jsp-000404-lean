import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s4 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s5 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2765 | h2765
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2766 | h2766
      · linarith only [h2766, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2768 | h2768
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2769 | h2769
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2770 | h2770
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2771 | h2771
              · linarith only [h0, h2765, h2771, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2773 | h2773
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2774 | h2774
                  · linarith only [h1, h2766, h2768, h2774, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2776 | h2776
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2777 | h2777
                      · linarith only [h0, h1, h2766, h2770, h2776, h2777, hc02, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2779 | h2779
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2780 | h2780
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2781 | h2781
                            · rcases h0bigk with h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2779, h2781, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h1, h2770, h2779, h2781, hc01, hc45, hlam, hphi, ht0b, ht5b, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2779, h2781, h4, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                rcases p2782_3 (m.d 0 1) (by simp) with h2787 | h2787
                                · rcases p2782_3 (m.d 0 2) (by simp) with h2788 | h2788
                                  · linarith only [h0, h2788, hlam]
                                  · linarith only [h2765, h2788, hlam]
                                · linarith only [h2787, h3, hlam]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h0, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h1, h2770, h2779, h2781, hc02, hc45, hlam, hphi, ht0b, ht5b, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h5, hlam, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2777, h5, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h1, hlam, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h4, hlam, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2766, hlam, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2765, h2777, h2779, h2781, h4, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2777, h5, hc02, hc34, hlam, hphi, ht23, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2777, h5, hc03, hc34, hlam, hphi, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                rcases p2782_3 (m.d 0 1) (by simp) with h2806 | h2806
                                · rcases p2782_3 (m.d 0 2) (by simp) with h2807 | h2807
                                  · linarith only [h2807, h5, hlam]
                                  · linarith only [h2765, h2807, hlam]
                                · linarith only [h2806, h3, hlam]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h3, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2765, hlam, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2768, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2769, hlam, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [hlam, p2782_0]
                            · linarith only [h0, h2770, h2777, h2779, h2781, h5, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h2768, h2769, h2780, h4, h5, hlam]
                        · linarith only [h2768, h2777, h2779, h4, h5, hc23, hc34, hlam, hphi]
                    · linarith only [h2766, h2768, h2770, h2776, hc23, hc34, hlam, hphi]
                · linarith only [h2765, h2770, h2773, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h2770, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h2768, h2769, h4, h5, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2823 | h2823
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2824 | h2824
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2825 | h2825
              · linarith only [h0, h2825, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2827 | h2827
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2828 | h2828
                  · linarith only [h1, h2766, h2828, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2830 | h2830
                    · linarith only [h1, h2768, h2830, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2832 | h2832
                      · linarith only [h2766, h2832, h4, h5, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2834 | h2834
                        · linarith only [h1, h2768, h2824, h2834, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2836 | h2836
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2837 | h2837
                            · rcases h0bigk with h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c | h2838c
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [hlam, p2838_0]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                rcases p2838_3 (m.d 0 1) (by simp) with h2841 | h2841
                                · rcases p2838_3 (m.d 0 2) (by simp) with h2842 | h2842
                                  · linarith only [h0, h2842, hlam]
                                  · linarith only [h2842, h4, hlam]
                                · linarith only [h1, h2841, hlam]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h0, h2827, h2834, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                rcases p2838_3 (m.d 0 1) (by simp) with h2847 | h2847
                                · rcases p2838_3 (m.d 0 2) (by simp) with h2848 | h2848
                                  · linarith only [h0, h2848, hlam]
                                  · linarith only [h2765, h2848, hlam]
                                · linarith only [h2847, h3, hlam]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h0, hlam, p2838_0]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [hlam, p2838_0]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h5, hlam, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h1, h2768, h2832, h5, hc13, hc34, hlam, hphi, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h1, hlam, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h4, hlam, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [hlam, p2838_0]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h2766, hlam, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h2768, hlam, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h2, hlam, p2838_0]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h0, h2827, h2834, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h1, h2832, h5, hc13, hc34, hlam, hphi, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [hlam, p2838_0]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h1, h2768, h2832, h5, hc13, hc34, hlam, hphi, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h3, hlam, p2838_0]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h2765, hlam, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h1, h2765, h2832, h5, hc13, hc34, hlam, hphi, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [h2823, hlam, p2838_1]
                              · have p2838_0 := h2838c.1
                                have p2838_1 := h2838c.2.1
                                have p2838_2 := h2838c.2.2.1
                                have p2838_3 := h2838c.2.2.2
                                linarith only [hlam, p2838_0]
                            · linarith only [h0, h2827, h2832, h2836, h2837, h5, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h2827, h2834, h2836, h5, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h2765, h2827, h5, hc12, hc24, hlam, hphi]
            · linarith only [h2824, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h2765, h2823, h5, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2877 | h2877
      · linarith only [h2877, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2879 | h2879
        · linarith only [h2765, h2879, h4, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2881 | h2881
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2882 | h2882
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2883 | h2883
              · linarith only [h0, h2883, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2885 | h2885
                · linarith only [h0, h2765, h2885, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2887 | h2887
                  · linarith only [h1, h2877, h2887, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2889 | h2889
                    · linarith only [h1, h2879, h2889, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2891 | h2891
                      · linarith only [h0, h1, h2877, h2882, h2891, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2893 | h2893
                        · linarith only [h2765, h2879, h2893, h4, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2895 | h2895
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2896 | h2896
                            · rcases h0bigk with h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c | h2897c
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [hlam, p2897_0]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h0, h2882, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                rcases p2897_3 (m.d 0 1) (by simp) with h2900 | h2900
                                · rcases p2897_3 (m.d 0 2) (by simp) with h2901 | h2901
                                  · linarith only [h0, h2901, hlam]
                                  · linarith only [h2901, h4, hlam]
                                · linarith only [h1, h2900, hlam]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h2, h2882, h2883, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h0, h2765, h2882, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h0, hlam, p2897_0]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [hlam, p2897_0]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h1, h2765, h2882, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h5, hlam, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h2765, hlam, p2897_0]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h1, hlam, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h4, hlam, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [hlam, p2897_0]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h2877, hlam, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h2879, hlam, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h2, hlam, p2897_0]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h0, h2882, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h1, h2882, h2891, h5, hc23, hc34, hlam, hphi, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [hlam, p2897_0]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h0, h2765, h2882, h2891, h5, hc23, hc34, hlam, hphi, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h3, hlam, p2897_0]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h0, h2882, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h1, h2765, h2882, h2893, hc23, hc35, hlam, hphi, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [h2881, hlam, p2897_1]
                              · have p2897_0 := h2897c.1
                                have p2897_1 := h2897c.2.1
                                have p2897_2 := h2897c.2.2.1
                                have p2897_3 := h2897c.2.2.2
                                linarith only [hlam, p2897_0]
                            · linarith only [h2881, h2891, h2896, h5, hlam]
                          · linarith only [h2881, h2895, h5, hlam]
            · linarith only [h2882, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2930 | h2930
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2931 | h2931
              · linarith only [h0, h2931, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2933 | h2933
                · linarith only [h0, h2765, h2933, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2935 | h2935
                  · linarith only [h1, h2877, h2935, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2937 | h2937
                    · linarith only [h1, h2879, h2937, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2939 | h2939
                      · linarith only [h0, h2877, h2881, h2930, h2939, h5, hc03, hc45, hlam, hphi, ht34]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2941 | h2941
                        · linarith only [h2879, h2881, h2941, h4, h5, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2943 | h2943
                          · linarith only [h0, h2881, h2930, h2939, h2943, h5, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h2930, h2943, h5, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h2930, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 9028000 in
set_option maxHeartbeats 9028000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s4 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 9028000 in
set_option maxHeartbeats 9028000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2947 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h2948 | h2948
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2949 | h2949
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2950 | h2950
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2951 | h2951
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2952 | h2952
          · linarith only [h0, h2947, h2952, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2954 | h2954
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2955 | h2955
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2956 | h2956
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2957 | h2957
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2958 | h2958
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2959 | h2959
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2960 | h2960
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2961 | h2961
                          · rcases h0bigk with h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c | h2962c
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [hlam, p2962_0]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h0, h2954, h2958, h2961, hc01, hc45, hlam, hphi, ht0b, ht5b, p2962_1]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h0, h2954, h2958, h2961, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2962_1]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h2947, h2958, h2961, hc01, hc45, hlam, hphi, ht0b, ht5b, p2962_1]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              rcases p2962_3 (m.d 0 1) (by simp) with h2967 | h2967
                              · rcases p2962_3 (m.d 0 2) (by simp) with h2968 | h2968
                                · linarith only [h0, h2968, hlam]
                                · linarith only [h2948, h2968, hlam]
                              · linarith only [h2967, h3, hlam]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h0, hlam, p2962_0]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [hlam, p2962_0]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h4, hlam, p2962_0]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h2, h2954, h2958, h2961, hc02, hc45, hlam, hphi, ht0b, ht5b, p2962_1]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2962_1]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h1, hlam, p2962_1]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p2962_1]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [hlam, p2962_0]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h2, h2954, h2958, h2961, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2962_1]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              rcases p2962_3 (m.d 0 1) (by simp) with h2981 | h2981
                              · rcases p2962_3 (m.d 0 2) (by simp) with h2982 | h2982
                                · linarith only [h2982, h4, hlam]
                                · linarith only [h2948, h2982, hlam]
                              · linarith only [h2981, h3, hlam]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h2, hlam, p2962_0]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h2947, hlam, p2962_0]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h2949, hlam, p2962_0]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [hlam, p2962_0]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h2947, h2955, h2959, h2961, h3, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2962_1]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h3, hlam, p2962_0]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h2948, hlam, p2962_1]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h2950, hlam, p2962_0]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [h2951, hlam, p2962_1]
                            · have p2962_0 := h2962c.1
                              have p2962_1 := h2962c.2.1
                              have p2962_2 := h2962c.2.2.1
                              have p2962_3 := h2962c.2.2.2
                              linarith only [hlam, p2962_0]
                          · linarith only [h0, h2954, h2960, h2961, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2997 | h2997
                          · linarith only [h1, h2956, h2960, h2997, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
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
                              linarith only [h2947, h2958, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2947, h2958, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2951, h2958, h2960, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2951, h2958, h2960, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h0, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h4, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2951, h2958, h2960, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h1, hlam, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2951, h2958, h2960, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2951, h2958, h2960, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2947, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2949, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2947, h2951, h2958, h2960, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h3, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2948, hlam, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2950, hlam, p2999_0]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [h2951, hlam, p2999_1]
                            · have p2999_0 := h2999c.1
                              have p2999_1 := h2999c.2.1
                              have p2999_2 := h2999c.2.2.1
                              have p2999_3 := h2999c.2.2.2
                              linarith only [hlam, p2999_0]
                      · linarith only [h2950, h2959, h4, hlam]
                    · linarith only [h2949, h2958, h4, hlam]
                  · linarith only [h2952, h2955, h2957, hlam]
                · linarith only [h2952, h2954, h2956, hlam]
              · linarith only [h2948, h2954, h2955, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h2947, h2954, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3031 | h3031
          · linarith only [h0, h2947, h3031, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3033 | h3033
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3034 | h3034
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3035 | h3035
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3036 | h3036
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3037 | h3037
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3038 | h3038
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3039 | h3039
                        · linarith only [h2, h2951, h3033, h3039, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3041 | h3041
                          · linarith only [h0, h2, h2951, h3034, h3037, h3039, h3041, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases h0bigk with h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h0, h3034, h3039, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h0, h3034, h3037, h3039, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              rcases p3043_3 (m.d 0 1) (by simp) with h3047 | h3047
                              · rcases p3043_3 (m.d 0 2) (by simp) with h3048 | h3048
                                · linarith only [h0, h3048, hlam]
                                · linarith only [h2947, h3048, hlam]
                              · linarith only [h2, h3047, hlam]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              rcases p3043_3 (m.d 0 1) (by simp) with h3052 | h3052
                              · rcases p3043_3 (m.d 0 2) (by simp) with h3053 | h3053
                                · linarith only [h0, h3053, hlam]
                                · linarith only [h2948, h3053, hlam]
                              · linarith only [h3, h3052, hlam]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h0, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h4, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h2, h3033, h3037, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h1, hlam, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h0, h3034, h3037, h3039, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              rcases p3043_3 (m.d 0 1) (by simp) with h3065 | h3065
                              · rcases p3043_3 (m.d 0 2) (by simp) with h3066 | h3066
                                · linarith only [h3066, h4, hlam]
                                · linarith only [h2947, h3066, hlam]
                              · linarith only [h2, h3065, hlam]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              rcases p3043_3 (m.d 0 1) (by simp) with h3070 | h3070
                              · rcases p3043_3 (m.d 0 2) (by simp) with h3071 | h3071
                                · linarith only [h3071, h4, hlam]
                                · linarith only [h2948, h3071, hlam]
                              · linarith only [h3, h3070, hlam]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h2, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h2947, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h2949, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h2951, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h3, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h2948, hlam, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h2950, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h2, h2948, h3033, h3037, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [hlam, p3043_0]
                      · linarith only [h2950, h3038, h4, hlam]
                    · linarith only [h2949, h3037, h4, hlam]
                  · linarith only [h3031, h3034, h3036, hlam]
                · linarith only [h2949, h2951, h3031, h3033, h3035, hc24, hc45, hlam, hphi]
              · linarith only [h2948, h3033, h3034, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h2947, h3033, h4, hc12, hc23, hlam, hphi]
      · linarith only [h2948, h2950, h4, hlam]
    · linarith only [h2947, h2949, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3093 | h3093
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3094 | h3094
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3095 | h3095
        · linarith only [h2947, h2948, h3095, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3097 | h3097
          · linarith only [h0, h2947, h3097, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3099 | h3099
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3100 | h3100
              · linarith only [h0, h2948, h3100, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3102 | h3102
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3103 | h3103
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3104 | h3104
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3105 | h3105
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3106 | h3106
                        · linarith only [h0, h2948, h3095, h3099, h3105, h3106, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3108 | h3108
                          · linarith only [h0, h2948, h3099, h3104, h3106, h3108, hlam]
                          · rcases h0bigk with h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c | h3110c
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h0, h3099, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3110_1]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h0, h2948, h3094, h3099, h3104, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3110_1]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              rcases p3110_3 (m.d 0 1) (by simp) with h3114 | h3114
                              · rcases p3110_3 (m.d 0 2) (by simp) with h3115 | h3115
                                · linarith only [h0, h3115, hlam]
                                · linarith only [h2947, h3115, hlam]
                              · linarith only [h2, h3114, hlam]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h0, h2948, h3099, h3104, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3110_1]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h0, hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h4, hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h2, h2948, h3099, h3104, h3105, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3110_1]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h2948, hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h1, hlam, p3110_1]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h0, h3099, h3104, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3110_1]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              rcases p3110_3 (m.d 0 1) (by simp) with h3128 | h3128
                              · rcases p3110_3 (m.d 0 2) (by simp) with h3129 | h3129
                                · linarith only [h3129, h4, hlam]
                                · linarith only [h2947, h3129, hlam]
                              · linarith only [h2, h3128, hlam]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h0, h2948, h3099, h3104, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3110_1]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h2, hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h2947, hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h3093, hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h3095, hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h3, hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h0, h3099, h3104, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p3110_1]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h3094, hlam, p3110_0]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [h2, h2948, h3099, h3104, h3106, hc34, hc45, hlam, hphi, p3110_1]
                            · have p3110_0 := h3110c.1
                              have p3110_1 := h3110c.2.1
                              have p3110_2 := h3110c.2.2.1
                              have p3110_3 := h3110c.2.2.2
                              linarith only [hlam, p3110_0]
                      · linarith only [h1, h3103, h3105, h4, hlam]
                    · linarith only [h0, h3093, h3099, h3104, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3146 | h3146
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3147 | h3147
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3148 | h3148
                        · linarith only [h3094, h3095, h3097, h3099, h3103, h3148, hc03, hc05, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3150 | h3150
                          · linarith only [h2948, h3094, h3097, h3099, h3103, h3146, h3148, h3150, hlam]
                          · rcases h0bigk with h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h0, h3099, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3152_1]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h3094, h3097, h3099, h3103, h3146, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3152_1]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              rcases p3152_3 (m.d 0 1) (by simp) with h3156 | h3156
                              · rcases p3152_3 (m.d 0 2) (by simp) with h3157 | h3157
                                · linarith only [h0, h3157, hlam]
                                · linarith only [h2947, h3157, hlam]
                              · linarith only [h2, h3156, hlam]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h3094, h3097, h3099, h3103, h3146, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3152_1]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h0, hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h4, hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3152_1]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h2948, hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h1, hlam, p3152_1]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h0, h3099, h3146, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3152_1]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              rcases p3152_3 (m.d 0 1) (by simp) with h3170 | h3170
                              · rcases p3152_3 (m.d 0 2) (by simp) with h3171 | h3171
                                · linarith only [h3171, h4, hlam]
                                · linarith only [h2947, h3171, hlam]
                              · linarith only [h2, h3170, hlam]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h3094, h3097, h3099, h3103, h3146, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3152_1]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h2, hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h2947, hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h3093, hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h3095, hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h3, hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h0, h3099, h3146, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p3152_1]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h3094, hlam, p3152_0]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [h2, h2948, h3099, h3146, h3148, hc34, hc45, hlam, hphi, p3152_1]
                            · have p3152_0 := h3152c.1
                              have p3152_1 := h3152c.2.1
                              have p3152_2 := h3152c.2.2.1
                              have p3152_3 := h3152c.2.2.2
                              linarith only [hlam, p3152_0]
                      · linarith only [h3094, h3147, h4, hlam]
                    · linarith only [h3094, h3097, h3099, h3103, h3146, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h3093, h3095, h3097, h3099, h3102, hc24, hc45, hlam, hphi]
            · linarith only [h2947, h2948, h3099, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3190 | h3190
        · linarith only [h2947, h2948, h3190, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3192 | h3192
          · linarith only [h0, h2947, h3192, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3194 | h3194
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3195 | h3195
              · linarith only [h0, h2948, h3195, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3197 | h3197
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3198 | h3198
                  · linarith only [h1, h3094, h3198, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3200 | h3200
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3201 | h3201
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3202 | h3202
                        · linarith only [h0, h3094, h3190, h3194, h3201, h3202, h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3204 | h3204
                          · linarith only [h0, h3094, h3194, h3200, h3201, h3202, h3204, h4, hlam]
                          · rcases h0bigk with h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c | h3206c
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h0, h3194, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3206_1]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h0, h3194, h3200, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3206_1]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              rcases p3206_3 (m.d 0 1) (by simp) with h3210 | h3210
                              · rcases p3206_3 (m.d 0 2) (by simp) with h3211 | h3211
                                · linarith only [h0, h3211, hlam]
                                · linarith only [h2947, h3211, hlam]
                              · linarith only [h2, h3210, hlam]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h0, h3094, h3194, h3200, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3206_1]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h0, hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h4, hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h2, h3094, h3194, h3200, h3201, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3206_1]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h2948, hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h1, hlam, p3206_1]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h3094, h3201, hc02, hc23, hlam, hphi, p3206_1]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h2, h3094, h3194, h3200, h3201, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3206_1]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h3094, hlam, p3206_1]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h2, hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h2947, hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h3093, hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h3190, hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h3, hlam, p3206_0]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h2947, h3200, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p3206_1]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h3094, h3201, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3206_1]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [h2, h3094, h3194, h3200, h3201, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3206_1]
                            · have p3206_0 := h3206c.1
                              have p3206_1 := h3206c.2.1
                              have p3206_2 := h3206c.2.2.1
                              have p3206_3 := h3206c.2.2.2
                              linarith only [hlam, p3206_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3236 | h3236
                        · linarith only [h0, h3194, h3201, h3236, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3238 | h3238
                          · linarith only [h0, h3194, h3200, h3201, h3236, h3238, h4, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h3194, h3200, h3201, h3238, h4, hc34, hc45, hlam, hphi]
                    · linarith only [h0, h3093, h3194, h3200, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h3093, h3094, h3192, h3194, h3197, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h2947, h2948, h3194, hc12, hc25, hlam, hphi]
    · linarith only [h2947, h3093, h4, hlam]

set_option maxHeartbeats 9028000 in
set_option maxHeartbeats 9028000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2947 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3245 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h3246 | h3246
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3247 | h3247
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3248 | h3248
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3249 | h3249
        · linarith only [h0, h3245, h3249, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3251 | h3251
          · linarith only [h0, h2947, h3251, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3253 | h3253
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3254 | h3254
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3255 | h3255
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3256 | h3256
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3257 | h3257
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3258 | h3258
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3259 | h3259
                        · rcases h0bigk with h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [hlam, p3260_0]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h3245, h3257, h3259, hc01, hc45, hlam, hphi, ht0b, ht5b, p3260_1]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h1, h3254, h3259, hc01, hc45, hlam, hphi, ht0b, ht5b, p3260_1]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h2947, h3245, h3257, h3259, hc01, hc45, hlam, hphi, ht0b, ht5b, p3260_1]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            rcases p3260_3 (m.d 0 1) (by simp) with h3265 | h3265
                            · rcases p3260_3 (m.d 0 2) (by simp) with h3266 | h3266
                              · linarith only [h0, h3266, hlam]
                              · linarith only [h3245, h3266, hlam]
                            · linarith only [h3, h3265, hlam]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h0, hlam, p3260_0]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [hlam, p3260_0]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h4, hlam, p3260_0]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h2947, hlam, p3260_1]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h2947, h3, h3256, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3260_1]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h1, hlam, p3260_1]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h4, hc02, hc23, hlam, hphi, p3260_1]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [hlam, p3260_0]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h0, h2947, h3253, h3257, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p3260_1]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            rcases p3260_3 (m.d 0 1) (by simp) with h3279 | h3279
                            · rcases p3260_3 (m.d 0 2) (by simp) with h3280 | h3280
                              · linarith only [h3280, h4, hlam]
                              · linarith only [h3245, h3280, hlam]
                            · linarith only [h3, h3279, hlam]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h2, hlam, p3260_0]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h0, h3253, h3257, h3259, hc04, hc45, hlam, hphi, ht0b, ht5b, p3260_1]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h3246, hlam, p3260_0]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [hlam, p3260_0]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            rcases p3260_3 (m.d 0 1) (by simp) with h3288 | h3288
                            · rcases p3260_3 (m.d 0 2) (by simp) with h3289 | h3289
                              · linarith only [h2947, h3289, hlam]
                              · linarith only [h3245, h3289, hlam]
                            · linarith only [h3, h3288, hlam]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h3, hlam, p3260_0]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h3245, hlam, p3260_1]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h3247, hlam, p3260_0]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [h3248, hlam, p3260_1]
                          · have p3260_0 := h3260c.1
                            have p3260_1 := h3260c.2.1
                            have p3260_2 := h3260c.2.2.1
                            have p3260_3 := h3260c.2.2.2
                            linarith only [hlam, p3260_0]
                        · rcases h0bigk with h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c | h3298c
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [hlam, p3298_0]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h0, h3253, h3258, h3259, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h0, h3253, h3258, h3259, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h2, h3251, h3253, h3258, h3259, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h3, h3253, h3258, h3259, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h0, hlam, p3298_0]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [hlam, p3298_0]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h4, hlam, p3298_0]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h2947, hlam, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h3, h3253, h3258, h3259, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h1, hlam, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h0, h3253, h3258, h3259, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [hlam, p3298_0]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h2, h3251, h3253, h3258, h3259, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h3, h3253, h3258, h3259, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h2, hlam, p3298_0]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h0, h3253, h3258, h3259, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h3246, hlam, p3298_0]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [hlam, p3298_0]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h2947, h3, h3253, h3256, h3258, h3259, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h3, hlam, p3298_0]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h3245, hlam, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h3247, hlam, p3298_0]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [h3248, hlam, p3298_1]
                          · have p3298_0 := h3298c.1
                            have p3298_1 := h3298c.2.1
                            have p3298_2 := h3298c.2.2.1
                            have p3298_3 := h3298c.2.2.2
                            linarith only [hlam, p3298_0]
                      · linarith only [h2947, h3248, h3258, hlam]
                    · linarith only [h3247, h3257, h4, hlam]
                  · linarith only [h3246, h3256, h4, hlam]
                · linarith only [h3249, h3253, h3255, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3328 | h3328
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3329 | h3329
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3330 | h3330
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3331 | h3331
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3332 | h3332
                        · rcases h0bigk with h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c | h3333c
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [hlam, p3333_0]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h3245, h3330, h3332, hc01, hc45, hlam, hphi, ht0b, ht5b, p3333_1]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h3246, h3254, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3333_1]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h2947, h3245, h3330, h3332, hc01, hc45, hlam, hphi, ht0b, ht5b, p3333_1]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            rcases p3333_3 (m.d 0 1) (by simp) with h3338 | h3338
                            · rcases p3333_3 (m.d 0 2) (by simp) with h3339 | h3339
                              · linarith only [h0, h3339, hlam]
                              · linarith only [h3245, h3339, hlam]
                            · linarith only [h3, h3338, hlam]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h0, hlam, p3333_0]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [hlam, p3333_0]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h4, hlam, p3333_0]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h2947, hlam, p3333_1]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3333_1]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h1, hlam, p3333_1]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h0, h3253, h3330, h3332, hc03, hc45, hlam, hphi, ht0b, ht5b, p3333_1]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [hlam, p3333_0]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h3246, h3249, h3253, h3254, h3330, h3332, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3333_1]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            rcases p3333_3 (m.d 0 1) (by simp) with h3352 | h3352
                            · rcases p3333_3 (m.d 0 2) (by simp) with h3353 | h3353
                              · linarith only [h3353, h4, hlam]
                              · linarith only [h3245, h3353, hlam]
                            · linarith only [h3, h3352, hlam]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h2, hlam, p3333_0]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h0, h3253, h3330, h3332, hc04, hc45, hlam, hphi, ht0b, ht5b, p3333_1]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h3246, hlam, p3333_0]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [hlam, p3333_0]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            rcases p3333_3 (m.d 0 1) (by simp) with h3361 | h3361
                            · rcases p3333_3 (m.d 0 2) (by simp) with h3362 | h3362
                              · linarith only [h2947, h3362, hlam]
                              · linarith only [h3245, h3362, hlam]
                            · linarith only [h3, h3361, hlam]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h3, hlam, p3333_0]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h3245, hlam, p3333_1]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h3247, hlam, p3333_0]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [h3248, hlam, p3333_1]
                          · have p3333_0 := h3333c.1
                            have p3333_1 := h3333c.2.1
                            have p3333_2 := h3333c.2.2.1
                            have p3333_3 := h3333c.2.2.2
                            linarith only [hlam, p3333_0]
                        · linarith only [h2947, h3248, h3249, h3253, h3254, h3329, h3330, h3332, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h2947, h3248, h3331, hlam]
                    · linarith only [h3247, h3330, h4, hlam]
                  · linarith only [h3246, h3329, h4, hlam]
                · linarith only [h3249, h3253, h3328, hlam]
            · linarith only [h3245, h3253, h4, hc12, hc23, hlam, hphi]
      · linarith only [h2947, h3245, h3248, hlam]
    · linarith only [h3245, h3247, h4, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3379 | h3379
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3380 | h3380
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3381 | h3381
        · linarith only [h0, h3381, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3383 | h3383
          · linarith only [h0, h2947, h3245, h3383, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3385 | h3385
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3386 | h3386
              · linarith only [h1, h3246, h3386, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3388 | h3388
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3389 | h3389
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3390 | h3390
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3391 | h3391
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3392 | h3392
                        · rcases h0bigk with h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c | h3393c
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [hlam, p3393_0]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h0, h3385, h3390, h3392, hc01, hc45, hlam, hphi, ht0b, ht5b, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h0, h3385, h3390, h3392, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h0, h3246, h3385, h3390, h3392, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            rcases p3393_3 (m.d 0 1) (by simp) with h3398 | h3398
                            · rcases p3393_3 (m.d 0 2) (by simp) with h3399 | h3399
                              · linarith only [h0, h3399, hlam]
                              · linarith only [h3245, h3399, hlam]
                            · linarith only [h3, h3398, hlam]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h0, hlam, p3393_0]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [hlam, p3393_0]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h4, hlam, p3393_0]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h2947, hlam, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h3, h3246, h3389, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h1, hlam, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h0, h3246, h3389, hc12, hc23, hlam, hphi, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [hlam, p3393_0]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h3246, hlam, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h3245, h3246, h3389, h3390, h3392, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h2, hlam, p3393_0]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h0, h3385, h3390, h3392, hc04, hc45, hlam, hphi, ht0b, ht5b, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h3246, h3389, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [hlam, p3393_0]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h3245, h3246, h3389, h3390, h3392, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h3, hlam, p3393_0]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h3245, hlam, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h3379, hlam, p3393_0]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [h3380, hlam, p3393_1]
                          · have p3393_0 := h3393c.1
                            have p3393_1 := h3393c.2.1
                            have p3393_2 := h3393c.2.2.1
                            have p3393_3 := h3393c.2.2.2
                            linarith only [hlam, p3393_0]
                        · linarith only [h0, h3246, h3380, h3385, h3390, h3392, h4, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h2947, h3245, h3380, h3391, hlam]
                    · linarith only [h3379, h3390, h4, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3426 | h3426
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3427 | h3427
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3428 | h3428
                        · rcases h0bigk with h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [hlam, p3429_0]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h0, h3385, h3426, h3428, hc01, hc45, hlam, hphi, ht0b, ht5b, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h0, h3385, h3426, h3428, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h0, h2947, h3385, h3426, h3428, hc01, hc45, hlam, hphi, ht0b, ht5b, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            rcases p3429_3 (m.d 0 1) (by simp) with h3434 | h3434
                            · rcases p3429_3 (m.d 0 2) (by simp) with h3435 | h3435
                              · linarith only [h0, h3435, hlam]
                              · linarith only [h3245, h3435, hlam]
                            · linarith only [h3, h3434, hlam]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h0, hlam, p3429_0]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [hlam, p3429_0]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h4, hlam, p3429_0]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h2947, hlam, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h3389, h4, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h1, hlam, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h0, h3246, h3385, hc04, hc25, hlam, hphi, ht0b, ht5b, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [hlam, p3429_0]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h3246, hlam, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h3245, h3389, h3426, h3428, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h2, hlam, p3429_0]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h2947, h3389, hc02, hc34, hlam, hphi, ht23, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h2947, h3389, hc03, hc34, hlam, hphi, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [hlam, p3429_0]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            rcases p3429_3 (m.d 0 1) (by simp) with h3453 | h3453
                            · rcases p3429_3 (m.d 0 2) (by simp) with h3454 | h3454
                              · linarith only [h2947, h3454, hlam]
                              · linarith only [h3245, h3454, hlam]
                            · linarith only [h3, h3453, hlam]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h3, hlam, p3429_0]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h3245, hlam, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h3379, hlam, p3429_0]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [h3380, hlam, p3429_1]
                          · have p3429_0 := h3429c.1
                            have p3429_1 := h3429c.2.1
                            have p3429_2 := h3429c.2.2.1
                            have p3429_3 := h3429c.2.2.2
                            linarith only [hlam, p3429_0]
                        · linarith only [h3389, h3428, h4, hc02, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h2947, h3245, h3380, h3427, hlam]
                    · linarith only [h0, h3379, h3385, h3426, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h3246, h3379, h3381, h3385, h3388, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
            · linarith only [h3245, h3246, h3385, h4, hc12, hc34, hlam, hphi, ht23]
      · linarith only [h3245, h3246, h3380, h4, hlam]
    · linarith only [h3245, h3379, h4, hlam]

end R2N4
