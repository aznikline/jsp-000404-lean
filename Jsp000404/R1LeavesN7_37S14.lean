import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_37S12
import Jsp000404.R1LeavesN7_37S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2108 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2780 | h2780
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2781 | h2781
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2782 | h2782
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2783 | h2783
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2784 | h2784
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2785 | h2785
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2786 | h2786
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2787 | h2787
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2788 | h2788
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2789 | h2789
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2790 | h2790
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2791 | h2791
                        · linarith only [h0, h2780, h2791, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h2108, h2780, h2785, h2786, h2787, h2791, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h2108, h2781, h2790, hlam]
                    · linarith only [h2108, h2781, h2782, h2784, h2789, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h2108, h2780, h2786, h2787, h2788, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h2108, h2780, h2786, h2787, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
              · linarith only [h0, h2782, h2786, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2799 | h2799
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2800 | h2800
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2801 | h2801
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2802 | h2802
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2803 | h2803
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2804 | h2804
                        · linarith only [h2108, h2780, h2785, h2804, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2806 | h2806
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2807 | h2807
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2808 | h2808
                              · linarith only [h2780, h2785, h2800, h2808, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2810 | h2810
                                · linarith only [h2780, h2785, h2800, h2806, h2810, hlam]
                                · rcases h2bigk with h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h0, hlam, p2812_1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h0, h2806, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2812_1, u2elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    rcases p2812_3 (m.d 0 2) (by simp) with h2816 | h2816
                                    · rcases p2812_3 (m.d 1 2) (by simp) with h2817 | h2817
                                      · rcases p2812_3 (m.d 2 3) (by simp) with h2818 | h2818
                                        · linarith only [h2782, h2818, hlam]
                                        · linarith only [h2806, h2818, hlam]
                                      · linarith only [h2800, h2817, hlam]
                                    · linarith only [h2816, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    rcases p2812_3 (m.d 0 2) (by simp) with h2823 | h2823
                                    · rcases p2812_3 (m.d 1 2) (by simp) with h2824 | h2824
                                      · rcases p2812_3 (m.d 2 3) (by simp) with h2825 | h2825
                                        · linarith only [h2782, h2825, hlam]
                                        · linarith only [h2807, h2825, hlam]
                                      · linarith only [h2801, h2824, hlam]
                                    · linarith only [h2823, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2812_1, u2elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2807, h2810, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2812_1, u2elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    rcases p2812_3 (m.d 0 2) (by simp) with h2833 | h2833
                                    · linarith only [h0, h2833, hlam]
                                    · linarith only [h2783, h2833, hlam]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    rcases p2812_3 (m.d 0 2) (by simp) with h2836 | h2836
                                    · linarith only [h0, h2836, hlam]
                                    · linarith only [h2108, h2781, h2782, h2799, h2801, h2807, h2810, h2836, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2782, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2799, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2782, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2812_1, u2elo0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h0, h2782, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2812_1, u2elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2783, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2800, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2806, hlam, p2812_1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2808, hlam, p2812_1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2812_1, u2elo4]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2801, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2807, hlam, p2812_1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2108, h2781, h2799, h2801, h2806, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2812_1, u2elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hlam, p2812_0]
                            · linarith only [h2108, h2781, h2799, h2803, h2807, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h2108, h2781, h2799, h2802, h2804, h2806, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h2108, h2781, h2803, hlam]
                    · linarith only [h2108, h2780, h2782, h2784, h2802, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h2780, h2800, h2801, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h2108, h2799, h2800, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h2780, h2799, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h2108, h2780, h2784, hlam]
        · linarith only [h0, h2780, h2783, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2863 | h2863
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2864 | h2864
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2865 | h2865
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2866 | h2866
              · linarith only [h0, h2782, h2866, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h2780, h2865, h2866, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2869 | h2869
              · linarith only [h0, h2782, h2869, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h2780, h2869, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h0, h2780, h2782, h2864, hlam]
        · linarith only [h0, h2780, h2863, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2874 | h2874
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2875 | h2875
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2876 | h2876
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2877 | h2877
            · linarith only [h2780, h2781, h2877, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2879 | h2879
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2880 | h2880
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2881 | h2881
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2882 | h2882
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2883 | h2883
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2884 | h2884
                        · linarith only [h2780, h2781, h2877, h2879, h2883, h2884, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2886 | h2886
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2887 | h2887
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2888 | h2888
                              · linarith only [h2780, h2781, h2880, h2884, h2888, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2890 | h2890
                                · linarith only [h2780, h2781, h2880, h2884, h2886, h2890, hlam]
                                · rcases h2bigk with h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [hlam, p2892_0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h0, hlam, p2892_1]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h0, h2887, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2892_1, u2elo1]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    rcases p2892_3 (m.d 0 2) (by simp) with h2896 | h2896
                                    · rcases p2892_3 (m.d 1 2) (by simp) with h2897 | h2897
                                      · rcases p2892_3 (m.d 2 3) (by simp) with h2898 | h2898
                                        · linarith only [h2874, h2898, hlam]
                                        · linarith only [h2886, h2898, hlam]
                                      · linarith only [h2880, h2897, hlam]
                                    · linarith only [h2896, hlam, p2892_0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    rcases p2892_3 (m.d 0 2) (by simp) with h2903 | h2903
                                    · rcases p2892_3 (m.d 1 2) (by simp) with h2904 | h2904
                                      · rcases p2892_3 (m.d 2 3) (by simp) with h2905 | h2905
                                        · linarith only [h2874, h2905, hlam]
                                        · linarith only [h2887, h2905, hlam]
                                      · linarith only [h2881, h2904, hlam]
                                    · linarith only [h2903, hlam, p2892_0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2892_1, u2elo1]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [hlam, p2892_0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2887, h2890, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2892_1, u2elo1]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    rcases p2892_3 (m.d 0 2) (by simp) with h2913 | h2913
                                    · linarith only [h0, h2913, hlam]
                                    · linarith only [h2875, h2913, hlam]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    rcases p2892_3 (m.d 0 2) (by simp) with h2916 | h2916
                                    · linarith only [h0, h2916, hlam]
                                    · linarith only [h2874, h2887, h2890, h2916, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2892_1, u2elo1]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2874, hlam, p2892_0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2879, hlam, p2892_0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [hlam, p2892_0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2874, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2892_1, u2elo0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2874, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2892_1, u2elo0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2875, hlam, p2892_0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2880, hlam, p2892_0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2886, hlam, p2892_1]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [hlam, p2892_0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2888, hlam, p2892_1]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2892_1, u2elo4]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2881, hlam, p2892_0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2887, hlam, p2892_1]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [h2874, h2886, h2887, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2892_1, u2elo0]
                                  · have p2892_0 := h2892c.1
                                    have p2892_1 := h2892c.2.1
                                    have p2892_2 := h2892c.2.2.1
                                    have p2892_3 := h2892c.2.2.2
                                    linarith only [hlam, p2892_0]
                            · linarith only [h2879, h2883, h2886, h2887, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h2780, h2781, h2879, h2882, h2883, h2886, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2936 | h2936
                        · linarith only [h0, h2780, h2936, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2938 | h2938
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2939 | h2939
                            · linarith only [h2108, h2780, h2880, h2883, h2938, h2939, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2941 | h2941
                              · linarith only [h2108, h2780, h2880, h2883, h2936, h2941, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2943 | h2943
                                · linarith only [h2108, h2780, h2880, h2883, h2936, h2938, h2943, hlam]
                                · linarith only [h2108, h2780, h2880, h2883, h2938, h2943, hc34, hc45, hlam, hphi]
                          · linarith only [h2108, h2876, h2883, h2938, hc23, hc35, hlam, hphi]
                    · linarith only [h2108, h2780, h2876, h2882, hlam]
                  · linarith only [h0, h2881, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h2108, h2780, h2879, h2880, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
              · linarith only [h0, h2780, h2879, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h2108, h2780, h2876, hlam]
        · linarith only [h0, h2780, h2875, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2953 | h2953
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2954 | h2954
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2955 | h2955
            · linarith only [h2780, h2781, h2955, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2957 | h2957
              · linarith only [h0, h2874, h2957, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h2780, h2957, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h0, h2780, h2874, h2954, hlam]
        · linarith only [h0, h2780, h2953, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2962 | h2962
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2963 | h2963
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2964 | h2964
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2965 | h2965
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2966 | h2966
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2967 | h2967
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2968 | h2968
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2969 | h2969
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2970 | h2970
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2971 | h2971
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2972 | h2972
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2973 | h2973
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2974 | h2974
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2975 | h2975
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2976 | h2976
                                · linarith only [h2963, h2973, h2976, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · linarith only [h0, h2962, h2972, h2976, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h2780, h2962, h2967, h2970, h2972, h2975, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h2780, h2962, h2967, h2970, h2971, h2974, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2981 | h2981
                            · linarith only [h2108, h2965, h2967, h2973, h2981, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h2780, h2962, h2967, h2970, h2971, h2981, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h2780, h2962, h2966, h2972, hc04, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h2780, h2962, h2970, h2971, hlam]
                    · linarith only [h2108, h2965, h2970, hlam]
                  · linarith only [h0, h2962, h2969, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                · linarith only [h2108, h2962, h2967, h2968, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
              · linarith only [h0, h2962, h2967, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h2780, h2962, h2966, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2991 | h2991
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2992 | h2992
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2993 | h2993
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2994 | h2994
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2995 | h2995
                    · linarith only [h2108, h2962, h2965, h2992, h2994, h2995, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2997 | h2997
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2998 | h2998
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2999 | h2999
                          · linarith only [h2108, h2962, h2963, h2965, h2994, h2999, hc02, hc25, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3001 | h3001
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3002 | h3002
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3003 | h3003
                                · rcases h2bigk with h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c | h3004c
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h0, hlam, p3004_1]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h0, h3001, h3003, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3004_1, u2elo1]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h0, h2999, h3001, h3003, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3004_1, u2elo1]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    rcases p3004_3 (m.d 0 2) (by simp) with h3009 | h3009
                                    · rcases p3004_3 (m.d 1 2) (by simp) with h3010 | h3010
                                      · rcases p3004_3 (m.d 2 3) (by simp) with h3011 | h3011
                                        · linarith only [h2963, h3011, hlam]
                                        · linarith only [h3001, h3011, hlam]
                                      · linarith only [h2994, h3010, hlam]
                                    · linarith only [h3009, hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3004_1, u2elo1]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h3001, h3003, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3004_1, u2elo1]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h2999, h3001, h3003, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3004_1, u2elo1]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    rcases p3004_3 (m.d 0 2) (by simp) with h3020 | h3020
                                    · linarith only [h0, h3020, hlam]
                                    · linarith only [h2108, h2962, h2964, h2994, h2999, h3001, h3003, h3020, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h2963, hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h2992, hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h2999, hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h2964, h2999, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3004_1, u2elo0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h2964, hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h2993, hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h0, h2964, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3004_1, u2elo1]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h0, h2964, h3001, h3003, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3004_1, u2elo1]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3004_1, u2elo4]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h2994, hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h3001, hlam, p3004_1]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [h3002, hlam, p3004_0]
                                  · have p3004_0 := h3004c.1
                                    have p3004_1 := h3004c.2.1
                                    have p3004_2 := h3004c.2.2.1
                                    have p3004_3 := h3004c.2.2.2
                                    linarith only [hlam, p3004_0]
                                · linarith only [h2108, h2995, h3003, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h2108, h2962, h2995, h2998, h3002, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h2108, h2962, h2995, h2997, h3001, hc23, hc34, hlam, hphi]
                        · linarith only [h2108, h2962, h2991, h2995, h2998, hc04, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h2108, h2962, h2997, hlam]
                  · linarith only [h0, h2962, h2994, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                · linarith only [h2108, h2962, h2992, h2993, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
              · linarith only [h0, h2962, h2992, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h2780, h2962, h2991, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3047 | h3047
          · linarith only [h2963, h2964, h3047, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3049 | h3049
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3050 | h3050
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3051 | h3051
                · linarith only [h2963, h2964, h3051, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h2962, h3051, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
              · linarith only [h0, h2962, h2963, h3050, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h2780, h2962, h3049, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3056 | h3056
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3057 | h3057
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3058 | h3058
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3059 | h3059
              · linarith only [h2963, h3059, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h2962, h3059, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h2780, h2962, h3058, hlam]
          · linarith only [h2963, h3056, h3057, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3064 | h3064
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3065 | h3065
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3066 | h3066
              · linarith only [h2963, h3066, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h2962, h3066, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h2780, h2962, h3065, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3070 | h3070
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3071 | h3071
              · linarith only [h0, h2962, h2963, h3071, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h0, h2962, h3071, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h2108, h2962, h3064, h3070, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3075 | h3075
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3076 | h3076
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3077 | h3077
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3078 | h3078
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3079 | h3079
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3080 | h3080
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3081 | h3081
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3082 | h3082
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3083 | h3083
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3084 | h3084
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3085 | h3085
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3086 | h3086
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3087 | h3087
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3088 | h3088
                                · linarith only [h3075, h3085, h3088, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · linarith only [h0, h3076, h3087, h3088, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3091 | h3091
                                · linarith only [h2108, h3077, h3079, h3087, h3091, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases h2bigk with h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [hlam, p3093_0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h0, hlam, p3093_1]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h0, h3086, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p3093_1, u2elo1]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    rcases p3093_3 (m.d 0 2) (by simp) with h3097 | h3097
                                    · rcases p3093_3 (m.d 1 2) (by simp) with h3098 | h3098
                                      · rcases p3093_3 (m.d 2 3) (by simp) with h3099 | h3099
                                        · linarith only [h3075, h3099, hlam]
                                        · linarith only [h3085, h3099, hlam]
                                      · linarith only [h3080, h3098, hlam]
                                    · linarith only [h3097, hlam, p3093_0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    rcases p3093_3 (m.d 0 2) (by simp) with h3104 | h3104
                                    · rcases p3093_3 (m.d 1 2) (by simp) with h3105 | h3105
                                      · rcases p3093_3 (m.d 2 3) (by simp) with h3106 | h3106
                                        · linarith only [h3075, h3106, hlam]
                                        · linarith only [h3086, h3106, hlam]
                                      · linarith only [h3081, h3105, hlam]
                                    · linarith only [h3104, hlam, p3093_0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3093_1, u2elo1]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [hlam, p3093_0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3086, h3091, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3093_1, u2elo1]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    rcases p3093_3 (m.d 0 2) (by simp) with h3114 | h3114
                                    · linarith only [h0, h3114, hlam]
                                    · linarith only [h3076, h3114, hlam]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    rcases p3093_3 (m.d 0 2) (by simp) with h3117 | h3117
                                    · linarith only [h0, h3117, hlam]
                                    · linarith only [h3075, h3077, h3078, h3085, h3087, h3117, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3093_1, u2elo1]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3075, hlam, p3093_0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3079, hlam, p3093_0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [hlam, p3093_0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3075, h3085, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3093_1, u2elo0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3075, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3093_1, u2elo0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3076, hlam, p3093_0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3080, hlam, p3093_0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3085, hlam, p3093_1]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [hlam, p3093_0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3087, hlam, p3093_1]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3093_1, u2elo4]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3081, hlam, p3093_0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3086, hlam, p3093_1]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [h3075, h3085, h3086, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3093_1, u2elo0]
                                  · have p3093_0 := h3093c.1
                                    have p3093_1 := h3093c.2.1
                                    have p3093_2 := h3093c.2.2.1
                                    have p3093_3 := h3093c.2.2.2
                                    linarith only [hlam, p3093_0]
                            · linarith only [h3079, h3083, h3085, h3086, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3136 | h3136
                            · linarith only [h2108, h3077, h3079, h3085, h3136, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3138 | h3138
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3139 | h3139
                                · rcases h2bigk with h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c | h3140c
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h0, hlam, p3140_1]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    rcases p3140_3 (m.d 0 2) (by simp) with h3143 | h3143
                                    · rcases p3140_3 (m.d 1 2) (by simp) with h3144 | h3144
                                      · rcases p3140_3 (m.d 2 3) (by simp) with h3145 | h3145
                                        · linarith only [h3145, hlam, p3140_0]
                                        · rcases p3140_3 (m.d 2 4) (by simp) with h3147 | h3147
                                          · linarith only [h3076, h3147, hlam]
                                          · linarith only [h3085, h3147, hlam]
                                      · linarith only [h3079, h3144, hlam]
                                    · linarith only [h3143, hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h0, h3138, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3140_1, u2elo1]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    rcases p3140_3 (m.d 0 2) (by simp) with h3153 | h3153
                                    · rcases p3140_3 (m.d 1 2) (by simp) with h3154 | h3154
                                      · rcases p3140_3 (m.d 2 3) (by simp) with h3155 | h3155
                                        · linarith only [h3075, h3155, hlam]
                                        · rcases p3140_3 (m.d 2 4) (by simp) with h3157 | h3157
                                          · linarith only [h3076, h3157, hlam]
                                          · linarith only [h3138, h3157, hlam]
                                      · linarith only [h3081, h3154, hlam]
                                    · linarith only [h3153, hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3140_1, u2elo1]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    rcases p3140_3 (m.d 0 2) (by simp) with h3164 | h3164
                                    · linarith only [h0, h3164, hlam]
                                    · linarith only [h3075, h3164, hlam]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h3138, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3140_1, u2elo1]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    rcases p3140_3 (m.d 0 2) (by simp) with h3168 | h3168
                                    · linarith only [h0, h3168, hlam]
                                    · linarith only [h3168, hc02, hlam, hphi, p3140_1, u2elo1]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h3075, hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h3079, hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h3085, hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h3136, hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h3076, hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h3080, hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h3076, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3140_1, u2elo0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h2108, h3077, h3079, h3085, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3140_1, u2elo1]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3140_1, u2elo4]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h3081, hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h3081, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3140_1, u2elo1]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [h3138, hlam, p3140_0]
                                  · have p3140_0 := h3140c.1
                                    have p3140_1 := h3140c.2.1
                                    have p3140_2 := h3140c.2.2.1
                                    have p3140_3 := h3140c.2.2.2
                                    linarith only [hlam, p3140_0]
                                · linarith only [h2780, h3078, h3079, h3082, h3085, h3139, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3187 | h3187
                                · linarith only [h2108, h3077, h3079, h3138, h3187, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · linarith only [h2780, h3078, h3079, h3082, h3085, h3187, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h2780, h3078, h3084, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3191 | h3191
                        · linarith only [h3082, h3083, h3191, hlam]
                        · linarith only [h2780, h3078, h3191, hlam]
                    · linarith only [h2108, h3077, h3082, hlam]
                  · linarith only [h0, h3081, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h3080, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h3079, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3198 | h3198
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3199 | h3199
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3200 | h3200
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3201 | h3201
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3202 | h3202
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3203 | h3203
                        · linarith only [h2780, h3078, h3198, h3201, h3203, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3205 | h3205
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3206 | h3206
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3207 | h3207
                              · linarith only [h2780, h3203, h3207, hc01, hlam, hphi, ht12, u2elo3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3209 | h3209
                                · linarith only [h3075, h3205, h3209, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · rcases h2bigk with h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [hlam, p3211_0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h0, hlam, p3211_1]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h0, h3206, h3209, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3211_1, u2elo1]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    rcases p3211_3 (m.d 0 2) (by simp) with h3215 | h3215
                                    · rcases p3211_3 (m.d 1 2) (by simp) with h3216 | h3216
                                      · rcases p3211_3 (m.d 2 3) (by simp) with h3217 | h3217
                                        · linarith only [h3075, h3217, hlam]
                                        · linarith only [h3205, h3217, hlam]
                                      · linarith only [h3199, h3216, hlam]
                                    · linarith only [h3215, hlam, p3211_0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    rcases p3211_3 (m.d 0 2) (by simp) with h3222 | h3222
                                    · rcases p3211_3 (m.d 1 2) (by simp) with h3223 | h3223
                                      · rcases p3211_3 (m.d 2 3) (by simp) with h3224 | h3224
                                        · linarith only [h3075, h3224, hlam]
                                        · linarith only [h3206, h3224, hlam]
                                      · linarith only [h3200, h3223, hlam]
                                    · linarith only [h3222, hlam, p3211_0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3211_1, u2elo1]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [hlam, p3211_0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3206, h3209, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3211_1, u2elo1]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    rcases p3211_3 (m.d 0 2) (by simp) with h3232 | h3232
                                    · linarith only [h0, h3232, hlam]
                                    · linarith only [h3076, h3232, hlam]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    rcases p3211_3 (m.d 0 2) (by simp) with h3235 | h3235
                                    · linarith only [h0, h3235, hlam]
                                    · linarith only [h3075, h3206, h3209, h3235, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3211_1, u2elo1]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3075, hlam, p3211_0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3198, hlam, p3211_0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [hlam, p3211_0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3075, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3211_1, u2elo0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3075, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3211_1, u2elo0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3076, hlam, p3211_0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3199, hlam, p3211_0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3205, hlam, p3211_1]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [hlam, p3211_0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3207, hlam, p3211_1]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3211_1, u2elo4]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3200, hlam, p3211_0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3206, hlam, p3211_1]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [h3075, h3205, h3206, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3211_1, u2elo0]
                                  · have p3211_0 := h3211c.1
                                    have p3211_1 := h3211c.2.1
                                    have p3211_2 := h3211c.2.2.1
                                    have p3211_3 := h3211c.2.2.2
                                    linarith only [hlam, p3211_0]
                            · linarith only [h3198, h3202, h3205, h3206, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3254 | h3254
                            · linarith only [h2108, h3077, h3198, h3205, h3254, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3256 | h3256
                              · linarith only [h2780, h3203, h3256, hc01, hlam, hphi, ht12, u2elo3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3258 | h3258
                                · linarith only [h2108, h2780, h3077, h3198, h3203, h3258, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases h2bigk with h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c | h3260c
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h0, hlam, p3260_1]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    rcases p3260_3 (m.d 0 2) (by simp) with h3263 | h3263
                                    · rcases p3260_3 (m.d 1 2) (by simp) with h3264 | h3264
                                      · rcases p3260_3 (m.d 2 3) (by simp) with h3265 | h3265
                                        · linarith only [h3265, hlam, p3260_0]
                                        · rcases p3260_3 (m.d 2 4) (by simp) with h3267 | h3267
                                          · linarith only [h3076, h3267, hlam]
                                          · linarith only [h3205, h3267, hlam]
                                      · linarith only [h3198, h3264, hlam]
                                    · linarith only [h3263, hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    rcases p3260_3 (m.d 0 2) (by simp) with h3272 | h3272
                                    · rcases p3260_3 (m.d 1 2) (by simp) with h3273 | h3273
                                      · rcases p3260_3 (m.d 2 3) (by simp) with h3274 | h3274
                                        · linarith only [h3075, h3274, hlam]
                                        · rcases p3260_3 (m.d 2 4) (by simp) with h3276 | h3276
                                          · linarith only [h3276, hlam, p3260_0]
                                          · rcases p3260_3 (m.d 2 5) (by simp) with h3278 | h3278
                                            · linarith only [h3198, h3202, h3254, h3278, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3260_1, u2elo1]
                                            · linarith only [h3256, h3278, hlam]
                                      · linarith only [h3199, h3273, hlam]
                                    · linarith only [h3272, hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    rcases p3260_3 (m.d 0 2) (by simp) with h3283 | h3283
                                    · rcases p3260_3 (m.d 1 2) (by simp) with h3284 | h3284
                                      · rcases p3260_3 (m.d 2 3) (by simp) with h3285 | h3285
                                        · linarith only [h3075, h3285, hlam]
                                        · rcases p3260_3 (m.d 2 4) (by simp) with h3287 | h3287
                                          · linarith only [h3076, h3287, hlam]
                                          · rcases p3260_3 (m.d 2 5) (by simp) with h3289 | h3289
                                            · linarith only [h3289, hlam, p3260_0]
                                            · rcases h4bigk with h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c | h3291c
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [hlam, p3291_0]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h2780, hlam, p3291_0]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h2780, h3203, h3205, hc23, hc45, hlam, hphi, ht34, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h2780, h3203, hc34, hc45, hlam, hphi, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3078, hlam, p3291_0]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3203, hc04, hc45, hlam, hphi, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [hlam, p3291_0]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3203, h3205, hc23, hc45, hlam, hphi, ht34, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3203, hc34, hc45, hlam, hphi, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3203, hlam, p3291_0]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3076, hlam, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3199, hlam, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [hlam, p3291_0]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3205, hlam, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3256, hlam, p3291_0]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3077, hlam, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3201, hlam, p3291_0]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h2780, h3077, h3203, h3205, hc23, hc45, hlam, hphi, ht34, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [hlam, p3291_0]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3258, hlam, p3291_0]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3077, h3205, hc23, hc45, hlam, hphi, ht34, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h0, h2780, h3205, h3256, hc01, hc23, hc45, hlam, hphi, ht12, ht34, p3260_1, p3291_1, u2elo1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                rcases p3291_3 (m.d 0 4) (by simp) with h3314 | h3314
                                                · linarith only [h3078, h3314, hlam]
                                                · linarith only [h3076, h3314, hlam]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [h3205, hc23, hc45, hlam, hphi, ht34, p3291_1]
                                              · have p3291_0 := h3291c.1
                                                have p3291_1 := h3291c.2.1
                                                have p3291_2 := h3291c.2.2.1
                                                have p3291_3 := h3291c.2.2.2
                                                linarith only [hlam, p3291_0]
                                      · linarith only [h3200, h3284, hlam]
                                    · linarith only [h3283, hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3260_1, u2elo1]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    rcases p3260_3 (m.d 0 2) (by simp) with h3323 | h3323
                                    · linarith only [h0, h3323, hlam]
                                    · linarith only [h3075, h3323, hlam]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    rcases p3260_3 (m.d 0 2) (by simp) with h3326 | h3326
                                    · linarith only [h0, h3326, hlam]
                                    · linarith only [h3076, h3326, hlam]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    rcases p3260_3 (m.d 0 2) (by simp) with h3329 | h3329
                                    · linarith only [h0, h3329, hlam]
                                    · linarith only [h3075, h3077, h3205, h3329, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3260_1, u2elo1]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3075, hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3198, hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3205, hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3254, hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3076, hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3199, hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3076, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3260_1, u2elo0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3256, hlam, p3260_1]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3198, h3202, h3254, hc02, hlam, hphi, p3260_1, u2elo1]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3200, hlam, p3260_0]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3198, h3202, h3254, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3260_1, u2elo1]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [h3198, h3202, h3254, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3260_1, u2elo1]
                                  · have p3260_0 := h3260c.1
                                    have p3260_1 := h3260c.2.1
                                    have p3260_2 := h3260c.2.2.1
                                    have p3260_3 := h3260c.2.2.2
                                    linarith only [hlam, p3260_0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3347 | h3347
                        · linarith only [h2780, h3078, h3199, h3347, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3349 | h3349
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3350 | h3350
                            · linarith only [h0, h3075, h3202, h3350, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3352 | h3352
                              · linarith only [h2780, h3347, h3352, hc01, hlam, hphi, ht12, u2elo3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3354 | h3354
                                · linarith only [h0, h2780, h3075, h3347, h3349, h3354, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases h2bigk with h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c | h3356c
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h0, hlam, p3356_1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h0, h3349, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3356_1, u2elo1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    rcases p3356_3 (m.d 0 2) (by simp) with h3360 | h3360
                                    · rcases p3356_3 (m.d 1 2) (by simp) with h3361 | h3361
                                      · rcases p3356_3 (m.d 2 3) (by simp) with h3362 | h3362
                                        · linarith only [h3075, h3362, hlam]
                                        · linarith only [h3349, h3362, hlam]
                                      · linarith only [h3199, h3361, hlam]
                                    · linarith only [h3360, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h0, h3349, h3350, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3356_1, u2elo1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3356_1, u2elo1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3349, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3356_1, u2elo1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    rcases p3356_3 (m.d 0 2) (by simp) with h3371 | h3371
                                    · linarith only [h0, h3371, hlam]
                                    · linarith only [h3076, h3371, hlam]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3349, h3350, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3356_1, u2elo1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3075, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3198, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3075, h3349, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3356_1, u2elo0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3350, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3076, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3199, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3349, hlam, p3356_1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3352, hlam, p3356_1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3356_1, u2elo4]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3200, hlam, p3356_0]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3200, h3349, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3356_1, u2elo1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [h3200, h3349, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3356_1, u2elo1]
                                  · have p3356_0 := h3356c.1
                                    have p3356_1 := h3356c.2.1
                                    have p3356_2 := h3356c.2.2.1
                                    have p3356_3 := h3356c.2.2.2
                                    linarith only [hlam, p3356_0]
                          · linarith only [h2108, h3077, h3202, h3349, hc23, hc35, hlam, hphi]
                    · linarith only [h2108, h3077, h3201, hlam]
                  · linarith only [h0, h3200, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h3199, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h3198, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3395 | h3395
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3396 | h3396
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3397 | h3397
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3398 | h3398
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3399 | h3399
                    · linarith only [h2108, h3077, h3396, h3399, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3401 | h3401
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3402 | h3402
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3403 | h3403
                          · linarith only [h3399, h3401, h3403, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3405 | h3405
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3406 | h3406
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3407 | h3407
                                · rcases h2bigk with h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h0, hlam, p3408_1]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3405, h3407, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3408_1, u2elo0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h0, h3403, h3405, h3407, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3408_1, u2elo1]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    rcases p3408_3 (m.d 0 2) (by simp) with h3413 | h3413
                                    · rcases p3408_3 (m.d 1 2) (by simp) with h3414 | h3414
                                      · rcases p3408_3 (m.d 2 3) (by simp) with h3415 | h3415
                                        · linarith only [h3075, h3415, hlam]
                                        · linarith only [h3405, h3415, hlam]
                                      · linarith only [h3398, h3414, hlam]
                                    · linarith only [h3413, hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3408_1, u2elo1]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3405, h3407, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3408_1, u2elo1]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3403, h3405, h3407, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3408_1, u2elo1]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    rcases p3408_3 (m.d 0 2) (by simp) with h3424 | h3424
                                    · linarith only [h0, h3424, hlam]
                                    · linarith only [h3076, h3403, h3405, h3407, h3424, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3408_1, u2elo1]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3075, hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3396, hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3403, hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3076, h3403, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3408_1, u2elo0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3076, hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3397, hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h0, h3076, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3408_1, u2elo1]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h0, h3076, h3405, h3407, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3408_1, u2elo1]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3408_1, u2elo4]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3398, hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3405, hlam, p3408_1]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [h3406, hlam, p3408_0]
                                  · have p3408_0 := h3408c.1
                                    have p3408_1 := h3408c.2.1
                                    have p3408_2 := h3408c.2.2.1
                                    have p3408_3 := h3408c.2.2.2
                                    linarith only [hlam, p3408_0]
                                · linarith only [h2962, h3399, h3401, h3407, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h0, h3076, h3395, h3403, h3405, h3406, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h3399, h3401, h3405, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h3076, h3395, h3399, h3401, h3402, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3446 | h3446
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3447 | h3447
                          · linarith only [h3075, h3077, h3447, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3449 | h3449
                            · linarith only [h0, h2108, h3076, h3401, h3447, h3449, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3451 | h3451
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3452 | h3452
                                · rcases h2bigk with h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c | h3453c
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h0, hlam, p3453_1]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    rcases p3453_3 (m.d 0 2) (by simp) with h3456 | h3456
                                    · rcases p3453_3 (m.d 1 2) (by simp) with h3457 | h3457
                                      · rcases p3453_3 (m.d 2 3) (by simp) with h3458 | h3458
                                        · linarith only [h3458, hlam, p3453_0]
                                        · rcases p3453_3 (m.d 2 4) (by simp) with h3460 | h3460
                                          · linarith only [h3076, h3460, hlam]
                                          · linarith only [h3447, h3460, hlam]
                                      · linarith only [h3396, h3457, hlam]
                                    · linarith only [h3456, hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h0, h3451, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3453_1, u2elo1]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    rcases p3453_3 (m.d 0 2) (by simp) with h3466 | h3466
                                    · rcases p3453_3 (m.d 1 2) (by simp) with h3467 | h3467
                                      · rcases p3453_3 (m.d 2 3) (by simp) with h3468 | h3468
                                        · linarith only [h3075, h3468, hlam]
                                        · rcases p3453_3 (m.d 2 4) (by simp) with h3470 | h3470
                                          · linarith only [h3076, h3470, hlam]
                                          · linarith only [h3451, h3470, hlam]
                                      · linarith only [h3398, h3467, hlam]
                                    · linarith only [h3466, hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3453_1, u2elo1]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    rcases p3453_3 (m.d 0 2) (by simp) with h3477 | h3477
                                    · linarith only [h0, h3477, hlam]
                                    · linarith only [h3075, h3477, hlam]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3451, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3453_1, u2elo1]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    rcases p3453_3 (m.d 0 2) (by simp) with h3481 | h3481
                                    · linarith only [h0, h3481, hlam]
                                    · linarith only [h3076, h3451, h3481, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3453_1, u2elo1]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3075, hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3396, hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3447, hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3449, hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3076, hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3397, hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3076, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3453_1, u2elo0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3076, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3453_1, u2elo0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3453_1, u2elo4]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3398, hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3398, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3453_1, u2elo1]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [h3451, hlam, p3453_0]
                                  · have p3453_0 := h3453c.1
                                    have p3453_1 := h3453c.2.1
                                    have p3453_2 := h3453c.2.2.1
                                    have p3453_3 := h3453c.2.2.2
                                    linarith only [hlam, p3453_0]
                                · linarith only [h3076, h3451, h3452, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3500 | h3500
                                · rcases h2bigk with h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h0, hlam, p3501_1]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    rcases p3501_3 (m.d 0 2) (by simp) with h3504 | h3504
                                    · rcases p3501_3 (m.d 1 2) (by simp) with h3505 | h3505
                                      · rcases p3501_3 (m.d 2 3) (by simp) with h3506 | h3506
                                        · linarith only [h3506, hlam, p3501_0]
                                        · rcases p3501_3 (m.d 2 4) (by simp) with h3508 | h3508
                                          · linarith only [h3076, h3508, hlam]
                                          · linarith only [h3447, h3508, hlam]
                                      · linarith only [h3396, h3505, hlam]
                                    · linarith only [h3504, hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    rcases p3501_3 (m.d 0 2) (by simp) with h3513 | h3513
                                    · rcases p3501_3 (m.d 1 2) (by simp) with h3514 | h3514
                                      · rcases p3501_3 (m.d 2 3) (by simp) with h3515 | h3515
                                        · linarith only [h3075, h3515, hlam]
                                        · rcases p3501_3 (m.d 2 4) (by simp) with h3517 | h3517
                                          · linarith only [h3517, hlam, p3501_0]
                                          · rcases p3501_3 (m.d 2 5) (by simp) with h3519 | h3519
                                            · linarith only [h3076, h3395, h3451, h3519, hlam]
                                            · linarith only [h3451, h3519, hlam]
                                      · linarith only [h3397, h3514, hlam]
                                    · linarith only [h3513, hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    rcases p3501_3 (m.d 0 2) (by simp) with h3524 | h3524
                                    · rcases p3501_3 (m.d 1 2) (by simp) with h3525 | h3525
                                      · rcases p3501_3 (m.d 2 3) (by simp) with h3526 | h3526
                                        · linarith only [h3075, h3526, hlam]
                                        · rcases p3501_3 (m.d 2 4) (by simp) with h3528 | h3528
                                          · linarith only [h3076, h3528, hlam]
                                          · rcases p3501_3 (m.d 2 5) (by simp) with h3530 | h3530
                                            · linarith only [h3530, hlam, p3501_0]
                                            · rcases h4bigk with h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c | h3532c
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [hlam, p3532_0]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h2780, hlam, p3532_0]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                rcases p3532_3 (m.d 0 4) (by simp) with h3535 | h3535
                                                · rcases p3532_3 (m.d 1 4) (by simp) with h3536 | h3536
                                                  · rcases p3532_3 (m.d 2 4) (by simp) with h3537 | h3537
                                                    · linarith only [h3076, h3537, hlam]
                                                    · rcases p3532_3 (m.d 3 4) (by simp) with h3539 | h3539
                                                      · rcases p3532_3 (m.d 4 5) (by simp) with h3540 | h3540
                                                        · linarith only [h3395, h3540, hlam]
                                                        · linarith only [h3451, h3540, hlam]
                                                      · linarith only [h3447, h3539, hlam]
                                                  · linarith only [h3397, h3536, hlam]
                                                · linarith only [h3076, h3535, hlam]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3077, hlam, p3532_0]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h0, h3076, h3451, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3532_1, u2elo1]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3395, h3451, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3532_1]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [hlam, p3532_0]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                rcases p3532_3 (m.d 0 4) (by simp) with h3550 | h3550
                                                · linarith only [h2780, h3550, hlam]
                                                · linarith only [h3076, h3550, hlam]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3399, hlam, p3532_1]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3397, h3447, h3451, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3532_1, u2elo1]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3076, hlam, p3532_1]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3397, hlam, p3532_1]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [hlam, p3532_0]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3447, hlam, p3532_1]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3451, hlam, p3532_0]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3395, h3447, h3451, hc23, hc34, hlam, hphi, p3532_1]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h2780, hc01, hc34, hlam, hphi, ht12, ht23, p3532_1]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                rcases p3532_3 (m.d 0 4) (by simp) with h3562 | h3562
                                                · linarith only [h3077, h3562, hlam]
                                                · linarith only [h3076, h3562, hlam]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [hlam, p3532_0]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3447, h3451, hc23, hc34, hlam, hphi, p3532_1]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3395, hlam, p3532_0]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3446, hlam, p3532_0]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h0, h3076, h3395, h3447, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3532_1, u2elo1]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [h3500, hlam, p3532_0]
                                              · have p3532_0 := h3532c.1
                                                have p3532_1 := h3532c.2.1
                                                have p3532_2 := h3532c.2.2.1
                                                have p3532_3 := h3532c.2.2.2
                                                linarith only [hlam, p3532_0]
                                      · linarith only [h3398, h3525, hlam]
                                    · linarith only [h3524, hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3501_1, u2elo1]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    rcases p3501_3 (m.d 0 2) (by simp) with h3576 | h3576
                                    · linarith only [h0, h3576, hlam]
                                    · linarith only [h3075, h3576, hlam]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    rcases p3501_3 (m.d 0 2) (by simp) with h3579 | h3579
                                    · linarith only [h0, h3579, hlam]
                                    · linarith only [h3076, h3579, hlam]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    rcases p3501_3 (m.d 0 2) (by simp) with h3582 | h3582
                                    · linarith only [h0, h3582, hlam]
                                    · linarith only [h3076, h3395, h3447, h3451, h3582, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3501_1, u2elo1]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h3075, hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h3396, hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h3447, hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h3449, hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h3076, hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h3397, hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h3076, h3395, h3451, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3501_1]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h3451, hlam, p3501_1]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h3076, h3395, h3451, hlam, p3501_1]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h3398, hlam, p3501_0]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h0, h3076, h3395, h3451, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3501_1, u2elo1]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [h0, h3076, h3395, h3451, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3501_1, u2elo1]
                                  · have p3501_0 := h3501c.1
                                    have p3501_1 := h3501c.2.1
                                    have p3501_2 := h3501c.2.2.1
                                    have p3501_3 := h3501c.2.2.2
                                    linarith only [hlam, p3501_0]
                                · linarith only [h0, h2108, h3076, h3077, h3395, h3500, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h2780, h3076, h3395, h3446, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h3398, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h2108, h3396, h3397, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h3396, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3605 | h3605
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3606 | h3606
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3607 | h3607
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3608 | h3608
                    · linarith only [h2108, h3077, h3605, h3608, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3610 | h3610
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3611 | h3611
                        · linarith only [h2780, h3395, h3606, h3611, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h3608, h3610, h3611, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3614 | h3614
                        · linarith only [h2108, h3077, h3395, h3606, h3614, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3616 | h3616
                          · linarith only [h3075, h3077, h3616, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3618 | h3618
                            · linarith only [h3076, h3610, h3616, h3618, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3620 | h3620
                              · linarith only [h0, h3076, h3614, h3620, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3622 | h3622
                                · linarith only [h2108, h3608, h3614, h3622, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h2108, h3608, h3622, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h3607, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h3076, h3606, hlam]
              · linarith only [h0, h3075, h3605, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3628 | h3628
          · linarith only [h3075, h3076, h3628, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3630 | h3630
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3631 | h3631
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3632 | h3632
                · linarith only [h3075, h3076, h3632, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h3632, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h3631, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3636 | h3636
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3637 | h3637
                · linarith only [h3076, h3637, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h3637, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h3636, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3641 | h3641
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3642 | h3642
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3643 | h3643
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3644 | h3644
              · linarith only [h3075, h3644, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h3644, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3647 | h3647
              · linarith only [h3075, h3641, h3647, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h0, h3647, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h3075, h3641, h3642, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3651 | h3651
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3652 | h3652
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3653 | h3653
              · linarith only [h3075, h3653, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h3653, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3656 | h3656
              · linarith only [h0, h3075, h3656, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h3656, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3659 | h3659
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3660 | h3660
              · linarith only [h0, h3075, h3660, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h3660, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3663 | h3663
              · linarith only [h0, h3075, h3663, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h3663, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h2108 | h2108
  · exact r1l7_22_14_M_LI_L_I_x1_x0 m hb2 hb4 h0 h2108
  · exact r1l7_22_14_M_LI_L_I_x1_x1 m hb2 hb4 h0 h2108

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_14_M_LI_L_I_x0 m hb2 hb4 h0
  · exact r1l7_22_14_M_LI_L_I_x1 m hb2 hb4 h0

end R2N4
