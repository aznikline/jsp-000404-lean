import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2150 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2802 | h2802
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2803 | h2803
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2804 | h2804
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2805 | h2805
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2806 | h2806
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2807 | h2807
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2808 | h2808
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2809 | h2809
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2810 | h2810
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2811 | h2811
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2812 | h2812
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2813 | h2813
                        · linarith only [h2150, h2802, h2813, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h2150, h2802, h2807, h2813, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h2150, h2812, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2150, h2802, h2805, h2811, hlam]
                  · linarith only [h2150, h2803, h2804, h2808, h2810, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h2150, h2802, h2808, h2809, hlam]
              · linarith only [h0, h2802, h2807, h2808, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2821 | h2821
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2822 | h2822
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2823 | h2823
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2824 | h2824
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2825 | h2825
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2826 | h2826
                        · linarith only [h2150, h2802, h2807, h2821, h2826, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2828 | h2828
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2829 | h2829
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2830 | h2830
                              · linarith only [h2802, h2807, h2822, h2830, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2832 | h2832
                                · linarith only [h2802, h2807, h2822, h2828, h2832, hlam]
                                · rcases h1bigk with h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c | h2834c
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [hlam, p2834_0]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h0, hlam, p2834_0]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2150, hlam, p2834_0]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2150, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2834_1, u3elo1]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2150, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2834_1, u3elo1]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    rcases p2834_3 (m.d 0 1) (by simp) with h2840 | h2840
                                    · linarith only [h2840, hlam, p2834_0]
                                    · rcases p2834_3 (m.d 1 2) (by simp) with h2842 | h2842
                                      · rcases p2834_3 (m.d 1 3) (by simp) with h2843 | h2843
                                        · linarith only [h2821, h2843, hlam]
                                        · linarith only [h2150, h2843, hlam]
                                      · linarith only [h2842, hlam, p2834_0]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [hlam, p2834_0]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2150, hc01, hc12, hlam, hphi, p2834_1]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    rcases p2834_3 (m.d 0 1) (by simp) with h2849 | h2849
                                    · linarith only [h0, h2849, hlam]
                                    · linarith only [h2802, h2849, hlam]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    rcases p2834_3 (m.d 0 1) (by simp) with h2852 | h2852
                                    · linarith only [h0, h2852, hlam]
                                    · linarith only [h2803, h2852, hlam]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2803, h2822, h2826, h2828, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2834_1, u3elo1]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2821, hlam, p2834_1]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [hlam, p2834_0]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    rcases p2834_3 (m.d 0 1) (by simp) with h2858 | h2858
                                    · linarith only [h2150, h2858, hlam]
                                    · linarith only [h2802, h2858, hlam]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    rcases p2834_3 (m.d 0 1) (by simp) with h2861 | h2861
                                    · linarith only [h2150, h2861, hlam]
                                    · linarith only [h2803, h2861, hlam]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2802, hlam, p2834_0]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2822, hlam, p2834_1]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2824, hlam, p2834_0]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [hlam, p2834_0]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2826, hlam, p2834_1]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2803, hlam, p2834_0]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2823, hlam, p2834_1]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h2825, hlam, p2834_0]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [h0, h2803, h2822, h2828, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2834_1]
                                  · have p2834_0 := h2834c.1
                                    have p2834_1 := h2834c.2.1
                                    have p2834_2 := h2834c.2.2.1
                                    have p2834_3 := h2834c.2.2.2
                                    linarith only [hlam, p2834_0]
                            · linarith only [h2150, h2806, h2829, hc23, hlam, hphi, u3elo1]
                          · linarith only [h2150, h2805, h2828, hc23, hlam, hphi, u3elo1]
                      · linarith only [h2150, h2825, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2150, h2824, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2804, h2823, hlam]
                · linarith only [h0, h2150, h2802, h2822, hc02, hlam, hphi, ht23, u3elo1]
              · linarith only [h0, h2821, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h2150, h2803, h2806, hlam]
        · linarith only [h2150, h2802, h2805, hlam]
      · linarith only [h0, h2803, h2804, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2884 | h2884
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2885 | h2885
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2886 | h2886
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2887 | h2887
            · linarith only [h2802, h2803, h2887, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2889 | h2889
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2890 | h2890
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2891 | h2891
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2892 | h2892
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2893 | h2893
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2894 | h2894
                        · linarith only [h2802, h2803, h2887, h2889, h2893, h2894, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2896 | h2896
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2897 | h2897
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2898 | h2898
                              · linarith only [h2802, h2803, h2890, h2894, h2898, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2900 | h2900
                                · linarith only [h2802, h2803, h2890, h2894, h2896, h2900, hlam]
                                · rcases h1bigk with h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c | h2902c
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [hlam, p2902_0]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h0, hlam, p2902_0]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2150, hlam, p2902_0]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2803, h2893, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2902_1, u3elo1]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2803, hlam, p2902_0]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    rcases p2902_3 (m.d 0 1) (by simp) with h2908 | h2908
                                    · linarith only [h2908, hlam, p2902_0]
                                    · rcases p2902_3 (m.d 1 2) (by simp) with h2910 | h2910
                                      · rcases p2902_3 (m.d 1 3) (by simp) with h2911 | h2911
                                        · linarith only [h2889, h2911, hlam]
                                        · linarith only [h2150, h2911, hlam]
                                      · linarith only [h2910, hlam, p2902_0]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [hlam, p2902_0]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2150, h2802, h2890, h2896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2902_1]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    rcases p2902_3 (m.d 0 1) (by simp) with h2917 | h2917
                                    · linarith only [h0, h2917, hlam]
                                    · linarith only [h2802, h2917, hlam]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2802, h2803, h2890, h2896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2902_1]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2802, h2890, h2896, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2902_1, u3elo1]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2889, hlam, p2902_1]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [hlam, p2902_0]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    rcases p2902_3 (m.d 0 1) (by simp) with h2924 | h2924
                                    · linarith only [h2150, h2924, hlam]
                                    · linarith only [h2802, h2924, hlam]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2802, h2803, h2890, h2896, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2902_1, u3elo1]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2802, hlam, p2902_0]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2890, hlam, p2902_1]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2892, hlam, p2902_0]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [hlam, p2902_0]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2894, hlam, p2902_1]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2802, h2890, h2894, h2896, hc34, hc45, hlam, hphi, p2902_1]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2891, hlam, p2902_1]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [h2893, hlam, p2902_0]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    rcases p2902_3 (m.d 0 1) (by simp) with h2936 | h2936
                                    · linarith only [h2803, h2936, hlam]
                                    · linarith only [h2802, h2936, hlam]
                                  · have p2902_0 := h2902c.1
                                    have p2902_1 := h2902c.2.1
                                    have p2902_2 := h2902c.2.2.1
                                    have p2902_3 := h2902c.2.2.2
                                    linarith only [hlam, p2902_0]
                            · linarith only [h2150, h2886, h2897, hc23, hlam, hphi, u3elo1]
                          · linarith only [h2150, h2885, h2896, hc23, hlam, hphi, u3elo1]
                      · linarith only [h2150, h2886, h2893, hlam]
                    · linarith only [h2150, h2892, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2802, h2884, h2890, h2891, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h2150, h2802, h2890, hc02, hlam, hphi, ht23, u3elo1]
              · linarith only [h0, h2889, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2947 | h2947
            · linarith only [h2150, h2802, h2886, h2947, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2949 | h2949
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2950 | h2950
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2951 | h2951
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2952 | h2952
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2953 | h2953
                      · linarith only [h2150, h2886, h2953, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h2150, h2802, h2950, h2953, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h2150, h2802, h2950, h2952, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h2150, h2802, h2884, h2949, h2950, h2951, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h2150, h2802, h2949, h2950, hlam]
              · linarith only [h0, h2949, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h2150, h2802, h2885, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2961 | h2961
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2962 | h2962
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2963 | h2963
            · linarith only [h0, h2802, h2884, h2963, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2965 | h2965
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2966 | h2966
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2967 | h2967
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2968 | h2968
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2969 | h2969
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2970 | h2970
                        · linarith only [h0, h2802, h2884, h2963, h2967, h2970, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2972 | h2972
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2973 | h2973
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2974 | h2974
                              · linarith only [h0, h2802, h2884, h2966, h2967, h2970, h2974, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2976 | h2976
                                · linarith only [h0, h2802, h2884, h2966, h2967, h2970, h2972, h2976, hlam]
                                · rcases h1bigk with h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c | h2978c
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [hlam, p2978_0]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h0, hlam, p2978_0]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h2150, hlam, p2978_0]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h0, h2884, h2967, h2969, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2978_1, u3elo1]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h2803, hlam, p2978_0]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    rcases p2978_3 (m.d 0 1) (by simp) with h2984 | h2984
                                    · linarith only [h2984, hlam, p2978_0]
                                    · rcases p2978_3 (m.d 1 2) (by simp) with h2986 | h2986
                                      · rcases p2978_3 (m.d 1 3) (by simp) with h2987 | h2987
                                        · linarith only [h2965, h2987, hlam]
                                        · linarith only [h2150, h2987, hlam]
                                      · linarith only [h2986, hlam, p2978_0]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [hlam, p2978_0]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h0, h2884, h2967, h2969, hc01, hc12, hlam, hphi, p2978_1]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h0, h2802, h2884, h2965, h2973, hlam, p2978_2]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h0, h2802, h2884, h2966, h2967, h2972, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2978_1]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h2802, h2966, h2972, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2978_1, u3elo1]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h2965, hlam, p2978_1]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [hlam, p2978_0]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    rcases p2978_3 (m.d 0 1) (by simp) with h2998 | h2998
                                    · linarith only [h2150, h2998, hlam]
                                    · linarith only [h2802, h2998, hlam]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h0, h2802, h2884, h2966, h2967, h2972, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2978_1, u3elo1]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h2802, hlam, p2978_0]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h2966, hlam, p2978_1]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h2968, hlam, p2978_0]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [hlam, p2978_0]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h2970, hlam, p2978_1]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h2802, h2966, h2970, h2972, hc34, hc45, hlam, hphi, p2978_1]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h2967, hlam, p2978_1]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [h2969, hlam, p2978_0]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    rcases p2978_3 (m.d 0 1) (by simp) with h3010 | h3010
                                    · linarith only [h2803, h3010, hlam]
                                    · linarith only [h2802, h3010, hlam]
                                  · have p2978_0 := h2978c.1
                                    have p2978_1 := h2978c.2.1
                                    have p2978_2 := h2978c.2.2.1
                                    have p2978_3 := h2978c.2.2.2
                                    linarith only [hlam, p2978_0]
                            · linarith only [h2962, h2973, hc23, hlam, hphi, u3elo0]
                          · linarith only [h2150, h2961, h2972, hc23, hlam, hphi, u3elo1]
                      · linarith only [h2150, h2969, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2150, h2802, h2966, h2968, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3018 | h3018
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3019 | h3019
                      · linarith only [h2965, h2967, h3019, hlam]
                      · linarith only [h2150, h2962, h3019, hlam]
                    · linarith only [h2150, h2802, h2966, h3018, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h2150, h2802, h2965, h2966, hlam]
              · linarith only [h0, h2965, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3025 | h3025
            · linarith only [h2802, h2803, h3025, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3027 | h3027
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3028 | h3028
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3029 | h3029
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3030 | h3030
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3031 | h3031
                      · linarith only [h2962, h3031, hc03, hlam, hphi, u3elo1]
                      · linarith only [h2150, h2802, h3028, h3031, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h2150, h2802, h3028, h3030, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3035 | h3035
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3036 | h3036
                      · linarith only [h2150, h2802, h2962, h3028, h3036, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h2150, h2802, h3028, h3036, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h2150, h2802, h3028, h3035, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h2150, h2802, h3027, h3028, hc23, hlam, hphi, u3elo0]
              · linarith only [h0, h3027, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h2150, h2802, h2961, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3043 | h3043
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3044 | h3044
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3045 | h3045
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3046 | h3046
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3047 | h3047
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3048 | h3048
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3049 | h3049
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3050 | h3050
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3051 | h3051
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3052 | h3052
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3053 | h3053
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3054 | h3054
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3055 | h3055
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3056 | h3056
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3057 | h3057
                                · rcases h1bigk with h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c | h3058c
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h0, hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h2150, hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h2802, hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h2150, h3050, h3055, h3057, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3058_1, u3elo1]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    rcases p3058_3 (m.d 0 1) (by simp) with h3064 | h3064
                                    · linarith only [h3064, hlam, p3058_0]
                                    · rcases p3058_3 (m.d 1 2) (by simp) with h3066 | h3066
                                      · rcases p3058_3 (m.d 1 3) (by simp) with h3067 | h3067
                                        · linarith only [h3048, h3067, hlam]
                                        · linarith only [h2150, h3067, hlam]
                                      · linarith only [h3066, hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h2802, h3051, hc01, hc12, hlam, hphi, p3058_1]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h2802, h3043, h3050, h3055, h3057, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3058_1]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    rcases p3058_3 (m.d 0 1) (by simp) with h3074 | h3074
                                    · linarith only [h0, h3074, hlam]
                                    · linarith only [h3043, h3074, hlam]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h3043, h3050, h3055, h3057, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3058_1, u3elo1]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h3048, hlam, p3058_1]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h2802, h3043, h3050, h3055, h3057, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3058_1, u3elo1]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    rcases p3058_3 (m.d 0 1) (by simp) with h3081 | h3081
                                    · linarith only [h2150, h3081, hlam]
                                    · linarith only [h3043, h3081, hlam]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h3043, h3050, h3051, h3055, h3057, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3058_1, u3elo1]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h3049, hlam, p3058_1]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h3051, hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    rcases p3058_3 (m.d 0 1) (by simp) with h3088 | h3088
                                    · linarith only [h2802, h3088, hlam]
                                    · linarith only [h3043, h3088, hlam]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h3043, hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h3050, hlam, p3058_1]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h3052, hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [h3053, hlam, p3058_0]
                                  · have p3058_0 := h3058c.1
                                    have p3058_1 := h3058c.2.1
                                    have p3058_2 := h3058c.2.2.1
                                    have p3058_3 := h3058c.2.2.2
                                    linarith only [hlam, p3058_0]
                                · linarith only [h2150, h3043, h3053, h3057, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · linarith only [h2802, h3043, h3051, h3053, h3056, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h3046, h3055, hc23, hlam, hphi, u3elo0]
                          · linarith only [h2150, h3045, h3054, hc23, hlam, hphi, u3elo1]
                        · linarith only [h2802, h3047, h3053, hlam]
                      · linarith only [h2802, h3051, h3052, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2150, h3043, h3045, h3051, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h2150, h3043, h3044, h3048, h3050, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3104 | h3104
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3105 | h3105
                    · linarith only [h3048, h3049, h3105, hlam]
                    · linarith only [h2150, h3043, h3104, h3105, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h3044, h3104, hlam]
              · linarith only [h0, h3048, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2802, h3043, h3047, hlam]
          · linarith only [h2150, h3043, h3046, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3112 | h3112
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3113 | h3113
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3114 | h3114
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3115 | h3115
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3116 | h3116
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3117 | h3117
                    · linarith only [h2150, h3045, h3117, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3043, h3116, h3117, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h3044, h3116, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3121 | h3121
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3122 | h3122
                    · linarith only [h2150, h3043, h3045, h3114, h3115, h3121, h3122, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h2150, h3043, h3121, h3122, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h3043, h3044, h3121, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h3043, h3114, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h2802, h3043, h3113, hlam]
          · linarith only [h2150, h3043, h3112, hlam]
      · linarith only [h0, h3043, h3044, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3130 | h3130
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3131 | h3131
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3132 | h3132
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3133 | h3133
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3134 | h3134
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3135 | h3135
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3136 | h3136
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3137 | h3137
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3138 | h3138
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3139 | h3139
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3140 | h3140
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3141 | h3141
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3142 | h3142
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3143 | h3143
                                · rcases h1bigk with h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c | h3144c
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h0, hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h2150, hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h2802, hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3043, hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    rcases p3144_3 (m.d 0 1) (by simp) with h3150 | h3150
                                    · linarith only [h3150, hlam, p3144_0]
                                    · rcases p3144_3 (m.d 1 2) (by simp) with h3152 | h3152
                                      · rcases p3144_3 (m.d 1 3) (by simp) with h3153 | h3153
                                        · linarith only [h3134, h3153, hlam]
                                        · linarith only [h2150, h3153, hlam]
                                      · linarith only [h3152, hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3043, h3137, h3139, hc01, hc12, hlam, hphi, p3144_1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3043, h3139, hc01, hc12, hlam, hphi, p3144_1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3043, hc01, hc12, hlam, hphi, p3144_1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p3144_1, u3elo1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3134, hlam, p3144_1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3043, h3139, hc01, hlam, hphi, ht12, ht23, p3144_1, u3elo1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3043, hc01, hlam, hphi, ht12, ht23, p3144_1, u3elo1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3137, hc01, hlam, hphi, ht12, ht23, p3144_1, u3elo1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3135, hlam, p3144_1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3137, hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3043, h3137, hc01, hlam, hphi, ht12, ht23, p3144_1, u3elo1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3138, hc01, hlam, hphi, ht12, ht23, p3144_1, u3elo1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3136, hlam, p3144_1]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3138, hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [h3139, hlam, p3144_0]
                                  · have p3144_0 := h3144c.1
                                    have p3144_1 := h3144c.2.1
                                    have p3144_2 := h3144c.2.2.1
                                    have p3144_3 := h3144c.2.2.2
                                    linarith only [hlam, p3144_0]
                                · rcases h1bigk with h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c | h3176c
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h0, hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h2150, hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h2802, hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3043, hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    rcases p3176_3 (m.d 0 1) (by simp) with h3182 | h3182
                                    · linarith only [h3182, hlam, p3176_0]
                                    · rcases p3176_3 (m.d 1 2) (by simp) with h3184 | h3184
                                      · rcases p3176_3 (m.d 1 3) (by simp) with h3185 | h3185
                                        · linarith only [h3134, h3185, hlam]
                                        · linarith only [h2150, h3185, hlam]
                                      · linarith only [h3184, hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h2150, hc01, hc12, hlam, hphi, p3176_1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h2802, h3133, h3143, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3176_1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3043, hc01, hc12, hlam, hphi, p3176_1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p3176_1, u3elo1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3134, hlam, p3176_1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h2802, h3133, h3143, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3176_1, u3elo1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3043, hc01, hlam, hphi, ht12, ht23, p3176_1, u3elo1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3137, hc01, hlam, hphi, ht12, ht23, p3176_1, u3elo1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3135, hlam, p3176_1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3137, hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3043, h3137, hc01, hlam, hphi, ht12, ht23, p3176_1, u3elo1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3138, hc01, hlam, hphi, ht12, ht23, p3176_1, u3elo1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3136, hlam, p3176_1]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3138, hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [h3139, hlam, p3176_0]
                                  · have p3176_0 := h3176c.1
                                    have p3176_1 := h3176c.2.1
                                    have p3176_2 := h3176c.2.2.1
                                    have p3176_3 := h3176c.2.2.2
                                    linarith only [hlam, p3176_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3208 | h3208
                                · linarith only [h2150, h3131, h3142, h3208, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · rcases h1bigk with h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c | h3210c
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h0, hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h2150, hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h2802, hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3043, hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    rcases p3210_3 (m.d 0 1) (by simp) with h3216 | h3216
                                    · linarith only [h3216, hlam, p3210_0]
                                    · rcases p3210_3 (m.d 1 2) (by simp) with h3218 | h3218
                                      · rcases p3210_3 (m.d 1 3) (by simp) with h3219 | h3219
                                        · linarith only [h3134, h3219, hlam]
                                        · linarith only [h2150, h3219, hlam]
                                      · linarith only [h3218, hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h2150, hc01, hc12, hlam, hphi, p3210_1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h2802, h3133, h3140, h3142, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3210_1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3043, hc01, hc12, hlam, hphi, p3210_1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p3210_1, u3elo1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3134, hlam, p3210_1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h2802, h3133, h3140, h3142, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3210_1, u3elo1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3043, hc01, hlam, hphi, ht12, ht23, p3210_1, u3elo1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3137, hc01, hlam, hphi, ht12, ht23, p3210_1, u3elo1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3135, hlam, p3210_1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3137, hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3043, h3137, hc01, hlam, hphi, ht12, ht23, p3210_1, u3elo1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3138, hc01, hlam, hphi, ht12, ht23, p3210_1, u3elo1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3136, hlam, p3210_1]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3138, hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [h3139, hlam, p3210_0]
                                  · have p3210_0 := h3210c.1
                                    have p3210_1 := h3210c.2.1
                                    have p3210_2 := h3210c.2.2.1
                                    have p3210_3 := h3210c.2.2.2
                                    linarith only [hlam, p3210_0]
                            · linarith only [h2150, h3132, h3141, hc23, hlam, hphi, u3elo1]
                          · linarith only [h2150, h3131, h3140, hc23, hlam, hphi, u3elo1]
                        · linarith only [h2802, h3133, h3139, hlam]
                      · linarith only [h2150, h3132, h3138, hlam]
                    · linarith only [h2150, h3131, h3137, hlam]
                  · linarith only [h0, h3130, h3136, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3248 | h3248
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3249 | h3249
                    · linarith only [h3134, h3135, h3249, hlam]
                    · linarith only [h2150, h3131, h3249, hlam]
                  · linarith only [h0, h3130, h3248, hlam]
              · linarith only [h0, h3134, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3254 | h3254
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3255 | h3255
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3256 | h3256
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3257 | h3257
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3258 | h3258
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3259 | h3259
                        · linarith only [h2802, h3133, h3257, h3259, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3261 | h3261
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3262 | h3262
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3263 | h3263
                              · linarith only [h3255, h3259, h3263, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3265 | h3265
                                · linarith only [h2802, h3130, h3259, h3261, h3263, h3265, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases h1bigk with h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c | h3267c
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [hlam, p3267_0]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h0, hlam, p3267_0]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h2150, hlam, p3267_0]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h2802, hlam, p3267_0]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h3043, hlam, p3267_0]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    rcases p3267_3 (m.d 0 1) (by simp) with h3273 | h3273
                                    · linarith only [h3273, hlam, p3267_0]
                                    · rcases p3267_3 (m.d 1 2) (by simp) with h3275 | h3275
                                      · rcases p3267_3 (m.d 1 3) (by simp) with h3276 | h3276
                                        · linarith only [h3254, h3276, hlam]
                                        · linarith only [h2150, h3276, hlam]
                                      · linarith only [h3275, hlam, p3267_0]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [hlam, p3267_0]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h2150, hc01, hc12, hlam, hphi, p3267_1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h2802, hc01, hc12, hlam, hphi, p3267_1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h3043, hc01, hc12, hlam, hphi, p3267_1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p3267_1, u3elo1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h3254, hlam, p3267_1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [hlam, p3267_0]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h2802, hc01, hlam, hphi, ht12, ht23, p3267_1, u3elo1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h3043, hc01, hlam, hphi, ht12, ht23, p3267_1, u3elo1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h3259, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3267_1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h3255, hlam, p3267_1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h3257, hlam, p3267_0]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [hlam, p3267_0]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h3259, hlam, p3267_1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h3258, hc01, hlam, hphi, ht12, ht23, p3267_1, u3elo1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h3256, hlam, p3267_1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h3258, hlam, p3267_0]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [h2802, h3258, hc01, hlam, hphi, ht12, ht23, p3267_1, u3elo1]
                                  · have p3267_0 := h3267c.1
                                    have p3267_1 := h3267c.2.1
                                    have p3267_2 := h3267c.2.2.1
                                    have p3267_3 := h3267c.2.2.2
                                    linarith only [hlam, p3267_0]
                            · linarith only [h2150, h3132, h3262, hc23, hlam, hphi, u3elo1]
                          · linarith only [h2150, h3131, h3261, hc23, hlam, hphi, u3elo1]
                      · linarith only [h2150, h3132, h3258, hlam]
                    · linarith only [h2150, h3131, h3257, hlam]
                  · linarith only [h0, h2150, h3130, h3132, h3256, hc01, hlam, hphi, ht12, ht23, u3elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3304 | h3304
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3305 | h3305
                    · linarith only [h3254, h3255, h3305, hlam]
                    · linarith only [h2150, h3131, h3305, hlam]
                  · linarith only [h0, h3130, h3304, hlam]
              · linarith only [h0, h3254, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3310 | h3310
            · linarith only [h3131, h3132, h3310, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3312 | h3312
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3313 | h3313
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3314 | h3314
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3315 | h3315
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3316 | h3316
                      · linarith only [h3132, h3316, hc03, hlam, hphi, u3elo1]
                      · linarith only [h2150, h3316, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2150, h3315, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h3130, h3314, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3321 | h3321
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3322 | h3322
                    · linarith only [h3312, h3313, h3322, hlam]
                    · linarith only [h3131, h3132, h3322, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h3130, h3321, hlam]
              · linarith only [h0, h3312, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3327 | h3327
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3328 | h3328
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3329 | h3329
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3330 | h3330
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3331 | h3331
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3332 | h3332
                    · linarith only [h3131, h3327, h3332, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h2150, h3332, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2802, h3130, h3327, h3330, h3331, hc01, hlam, hphi, ht12, ht23, u3elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3336 | h3336
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3337 | h3337
                    · linarith only [h3131, h3337, hc03, hlam, hphi, u3elo1]
                    · linarith only [h2150, h3337, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h3130, h3336, hlam]
              · linarith only [h0, h3329, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h3131, h3327, h3328, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3343 | h3343
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3344 | h3344
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3345 | h3345
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3346 | h3346
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3347 | h3347
                    · linarith only [h2150, h3131, h3347, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3347, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h3130, h3346, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3351 | h3351
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3352 | h3352
                    · linarith only [h2150, h3131, h3352, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3352, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h3130, h3351, hlam]
              · linarith only [h0, h3344, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3357 | h3357
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3358 | h3358
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3359 | h3359
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3360 | h3360
                    · linarith only [h2150, h3131, h3360, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3360, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h3130, h3359, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3364 | h3364
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3365 | h3365
                    · linarith only [h2150, h3131, h3365, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3365, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h3130, h3364, hlam]
              · linarith only [h0, h3357, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3370 | h3370
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3371 | h3371
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3372 | h3372
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3373 | h3373
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3374 | h3374
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3375 | h3375
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3376 | h3376
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3377 | h3377
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3378 | h3378
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3379 | h3379
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3380 | h3380
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3381 | h3381
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3382 | h3382
                                · rcases h1bigk with h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c | h3383c
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h0, hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h2150, hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h2802, hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h3043, hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    rcases p3383_3 (m.d 0 1) (by simp) with h3389 | h3389
                                    · linarith only [h3389, hlam, p3383_0]
                                    · rcases p3383_3 (m.d 1 2) (by simp) with h3391 | h3391
                                      · rcases p3383_3 (m.d 1 3) (by simp) with h3392 | h3392
                                        · linarith only [h3373, h3392, hlam]
                                        · linarith only [h2150, h3392, hlam]
                                      · linarith only [h3391, hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h2150, hc01, hc12, hlam, hphi, p3383_1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h2802, hc01, hc12, hlam, hphi, p3383_1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h0, h3130, h3375, hc01, hc12, hlam, hphi, p3383_1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p3383_1, u3elo1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h3373, hlam, p3383_1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h0, h3130, h3374, h3381, hc01, hlam, hphi, ht12, ht23, p3383_1, u3elo1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h0, h3130, h3375, hc01, hlam, hphi, ht12, ht23, p3383_1, u3elo1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h3376, hc01, hlam, hphi, ht12, ht23, p3383_1, u3elo1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h3374, hlam, p3383_1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h3376, hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h0, h3130, h3375, h3376, hc01, hlam, hphi, ht12, ht23, p3383_1, u3elo1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h3377, hc01, hlam, hphi, ht12, ht23, p3383_1, u3elo1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h3375, hlam, p3383_1]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h3377, hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [h3378, hlam, p3383_0]
                                  · have p3383_0 := h3383c.1
                                    have p3383_1 := h3383c.2.1
                                    have p3383_2 := h3383c.2.2.1
                                    have p3383_3 := h3383c.2.2.2
                                    linarith only [hlam, p3383_0]
                                · rcases h1bigk with h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c | h3415c
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h0, hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h2150, hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h2802, hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h3043, hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    rcases p3415_3 (m.d 0 1) (by simp) with h3421 | h3421
                                    · linarith only [h3421, hlam, p3415_0]
                                    · rcases p3415_3 (m.d 1 2) (by simp) with h3423 | h3423
                                      · rcases p3415_3 (m.d 1 3) (by simp) with h3424 | h3424
                                        · linarith only [h3373, h3424, hlam]
                                        · linarith only [h2150, h3424, hlam]
                                      · linarith only [h3423, hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h2150, h3370, h3372, h3382, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3415_1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h2802, hc01, hc12, hlam, hphi, p3415_1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h3043, hc01, hc12, hlam, hphi, p3415_1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p3415_1, u3elo1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h3373, hlam, p3415_1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h2802, h3372, h3382, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3415_1, u3elo1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h0, h3130, h3375, hc01, hlam, hphi, ht12, ht23, p3415_1, u3elo1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h3376, hc01, hlam, hphi, ht12, ht23, p3415_1, u3elo1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h3374, hlam, p3415_1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h3376, hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h0, h3130, h3375, h3376, hc01, hlam, hphi, ht12, ht23, p3415_1, u3elo1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h3377, hc01, hlam, hphi, ht12, ht23, p3415_1, u3elo1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h3375, hlam, p3415_1]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h3377, hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [h3378, hlam, p3415_0]
                                  · have p3415_0 := h3415c.1
                                    have p3415_1 := h3415c.2.1
                                    have p3415_2 := h3415c.2.2.1
                                    have p3415_3 := h3415c.2.2.2
                                    linarith only [hlam, p3415_0]
                              · linarith only [h0, h3130, h3370, h3372, h3381, hc01, hlam, hphi, ht12, ht23, u3elo0]
                            · linarith only [h2150, h3371, h3380, hc23, hlam, hphi, u3elo1]
                          · linarith only [h2150, h3370, h3379, hc23, hlam, hphi, u3elo1]
                        · linarith only [h2150, h2802, h3370, h3372, h3378, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h2150, h3371, h3377, hlam]
                    · linarith only [h2150, h3370, h3376, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3453 | h3453
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3454 | h3454
                      · linarith only [h3373, h3375, h3454, hlam]
                      · linarith only [h2150, h3371, h3454, hlam]
                    · linarith only [h2150, h3370, h3453, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3458 | h3458
                  · linarith only [h0, h3130, h3374, h3458, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3460 | h3460
                    · linarith only [h3373, h3374, h3460, hlam]
                    · linarith only [h2150, h3370, h3460, hlam]
              · linarith only [h0, h3373, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3464 | h3464
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3465 | h3465
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3466 | h3466
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3467 | h3467
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3468 | h3468
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3469 | h3469
                        · linarith only [h2802, h3372, h3467, h3469, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3471 | h3471
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3472 | h3472
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3473 | h3473
                              · linarith only [h3465, h3469, h3473, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3475 | h3475
                                · linarith only [h2802, h3469, h3475, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                · rcases h1bigk with h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [hlam, p3477_0]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h0, hlam, p3477_0]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h2150, hlam, p3477_0]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h2802, hlam, p3477_0]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h3043, hlam, p3477_0]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    rcases p3477_3 (m.d 0 1) (by simp) with h3483 | h3483
                                    · linarith only [h3483, hlam, p3477_0]
                                    · rcases p3477_3 (m.d 1 2) (by simp) with h3485 | h3485
                                      · rcases p3477_3 (m.d 1 3) (by simp) with h3486 | h3486
                                        · linarith only [h3464, h3486, hlam]
                                        · linarith only [h2150, h3486, hlam]
                                      · linarith only [h3485, hlam, p3477_0]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [hlam, p3477_0]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h0, h3130, h3466, h3468, hc01, hc12, hlam, hphi, p3477_1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h2802, hc01, hc12, hlam, hphi, p3477_1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h0, h3130, h3466, hc01, hc12, hlam, hphi, p3477_1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p3477_1, u3elo1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h3464, hlam, p3477_1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [hlam, p3477_0]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h2802, hc01, hlam, hphi, ht12, ht23, p3477_1, u3elo1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h0, h3130, h3466, hc01, hlam, hphi, ht12, ht23, p3477_1, u3elo1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h3469, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3477_1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h3465, hlam, p3477_1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h3467, hlam, p3477_0]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [hlam, p3477_0]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h3469, hlam, p3477_1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h3468, hc01, hlam, hphi, ht12, ht23, p3477_1, u3elo1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h3466, hlam, p3477_1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h3468, hlam, p3477_0]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [h2802, h3468, hc01, hlam, hphi, ht12, ht23, p3477_1, u3elo1]
                                  · have p3477_0 := h3477c.1
                                    have p3477_1 := h3477c.2.1
                                    have p3477_2 := h3477c.2.2.1
                                    have p3477_3 := h3477c.2.2.2
                                    linarith only [hlam, p3477_0]
                            · linarith only [h2150, h3371, h3472, hc23, hlam, hphi, u3elo1]
                          · linarith only [h2150, h3370, h3471, hc23, hlam, hphi, u3elo1]
                      · linarith only [h2150, h3371, h3468, hlam]
                    · linarith only [h2150, h3370, h3467, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3513 | h3513
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3514 | h3514
                      · linarith only [h3464, h3466, h3514, hlam]
                      · linarith only [h2150, h3371, h3514, hlam]
                    · linarith only [h2150, h3370, h3513, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3518 | h3518
                  · linarith only [h0, h3130, h3465, h3518, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3520 | h3520
                    · linarith only [h3464, h3465, h3520, hlam]
                    · linarith only [h2150, h3370, h3520, hlam]
              · linarith only [h0, h3464, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3524 | h3524
            · linarith only [h3370, h3371, h3524, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3526 | h3526
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3527 | h3527
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3528 | h3528
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3529 | h3529
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3530 | h3530
                      · linarith only [h3371, h3530, hc03, hlam, hphi, u3elo1]
                      · linarith only [h2150, h3530, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2150, h3529, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3534 | h3534
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3535 | h3535
                      · linarith only [h3371, h3535, hc03, hlam, hphi, u3elo1]
                      · linarith only [h2150, h3535, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2150, h3534, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3539 | h3539
                  · linarith only [h0, h3130, h3527, h3539, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3541 | h3541
                    · linarith only [h3526, h3527, h3541, hlam]
                    · linarith only [h3370, h3371, h3541, hc13, hlam, hphi, u3elo4]
              · linarith only [h0, h3526, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3545 | h3545
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3546 | h3546
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3547 | h3547
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3548 | h3548
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3549 | h3549
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3550 | h3550
                    · linarith only [h3370, h3545, h3550, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h2150, h3550, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3553 | h3553
                    · linarith only [h0, h3130, h3370, h3545, h3553, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3553, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3556 | h3556
                  · linarith only [h0, h3130, h3548, h3556, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3558 | h3558
                    · linarith only [h0, h3130, h3370, h3545, h3558, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3558, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h3547, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h3370, h3545, h3546, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3563 | h3563
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3564 | h3564
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3565 | h3565
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3566 | h3566
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3567 | h3567
                    · linarith only [h3370, h3567, hc03, hlam, hphi, u3elo1]
                    · linarith only [h2150, h3567, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3570 | h3570
                    · linarith only [h2150, h3370, h3570, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3570, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3573 | h3573
                  · linarith only [h0, h3130, h3565, h3573, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3575 | h3575
                    · linarith only [h2150, h3370, h3575, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3575, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h3564, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3579 | h3579
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3580 | h3580
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3581 | h3581
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3582 | h3582
                    · linarith only [h2150, h3370, h3582, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3582, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3585 | h3585
                    · linarith only [h2150, h3370, h3585, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3585, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3588 | h3588
                  · linarith only [h0, h3130, h3580, h3588, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3590 | h3590
                    · linarith only [h2150, h3370, h3590, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h2150, h3590, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h3579, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h2150 | h2150
  · exact r1l7_11_13_25_L_I_L_0_H_I_x1_x0 m hb1 hb3 hb5 h0 h2150
  · exact r1l7_11_13_25_L_I_L_0_H_I_x1_x1 m hb1 hb3 hb5 h0 h2150

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_I_L_0_H_I_x1 m hb1 hb3 hb5 h0

end R2N4
