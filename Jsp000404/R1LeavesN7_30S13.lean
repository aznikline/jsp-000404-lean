import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5764000 in
set_option maxHeartbeats 5764000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1106 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1991 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2808 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1106 := hg1106
  rcases m.htr 0 2 4 (by decide) (by decide) with h2809 | h2809
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2810 | h2810
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2811 | h2811
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2812 | h2812
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2813 | h2813
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2814 | h2814
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2815 | h2815
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2816 | h2816
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2817 | h2817
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2818 | h2818
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2819 | h2819
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2820 | h2820
                        · linarith only [h2808, h2820, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h2808, h2811, h2820, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h2808, h2811, h2813, h2819, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1106, h2811, h2812, h2818, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · linarith only [h1106, h2811, h2817, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h2810, h2816, hlam]
              · linarith only [h0, h2809, h2815, hlam]
            · linarith only [h0, h2808, h2814, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2829 | h2829
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2830 | h2830
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2831 | h2831
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2832 | h2832
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2833 | h2833
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2834 | h2834
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2835 | h2835
                        · linarith only [h2808, h2835, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h2808, h2811, h2835, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2838 | h2838
                        · linarith only [h2808, h2838, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h2811, h2838, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1106, h2812, h2833, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h1106, h2811, h2812, h2832, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h0, h2810, h2831, hlam]
              · linarith only [h0, h2809, h2830, hlam]
            · linarith only [h0, h2808, h2829, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2846 | h2846
          · linarith only [h2811, h2812, h2846, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2848 | h2848
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2849 | h2849
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2850 | h2850
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2851 | h2851
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2852 | h2852
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2853 | h2853
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2854 | h2854
                        · linarith only [h2808, h2854, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h2811, h2854, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2857 | h2857
                        · linarith only [h2808, h2857, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h2811, h2812, h2848, h2852, h2857, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2860 | h2860
                      · linarith only [h1991, h2846, h2851, h2852, h2860, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2862 | h2862
                        · linarith only [h2808, h2862, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h2810, h2811, h2812, h2862, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1106, h2810, h2811, h2812, h2851, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h2810, h2850, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h2809, h2810, h2849, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
            · linarith only [h0, h2808, h2848, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2869 | h2869
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2870 | h2870
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2871 | h2871
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2872 | h2872
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2873 | h2873
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2874 | h2874
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2875 | h2875
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2876 | h2876
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2877 | h2877
                        · linarith only [h2808, h2811, h2869, h2877, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2879 | h2879
                          · linarith only [h2809, h2877, h2879, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h2869, h2879, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h2809, h2870, h2876, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h2811, h2869, h2874, h2875, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2884 | h2884
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2885 | h2885
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2886 | h2886
                        · linarith only [h1106, h2874, h2886, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2888 | h2888
                          · linarith only [h2809, h2886, h2888, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h2869, h2888, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h2809, h2870, h2885, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1106, h2869, h2884, hlam]
                · linarith only [h2810, h2873, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h2809, h2872, hlam]
            · linarith only [h0, h2808, h2871, hlam]
          · linarith only [h2811, h2869, h2870, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2897 | h2897
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2898 | h2898
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2899 | h2899
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2900 | h2900
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2901 | h2901
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2902 | h2902
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2903 | h2903
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2904 | h2904
                        · linarith only [h2808, h2811, h2904, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2906 | h2906
                          · linarith only [h2808, h2869, h2906, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2908 | h2908
                            · linarith only [h2809, h2908, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h2897, h2908, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h2809, h2897, h2903, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1106, h2811, h2901, h2902, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2913 | h2913
                    · linarith only [h2869, h2901, h2913, hc03, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2915 | h2915
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2916 | h2916
                        · linarith only [h2808, h2916, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2918 | h2918
                          · linarith only [h2809, h2913, h2916, h2918, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2920 | h2920
                            · linarith only [h2809, h2920, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h2809, h2897, h2916, h2920, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h2809, h2897, h2915, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h0, h2810, h2900, hlam]
              · linarith only [h0, h2809, h2899, hlam]
            · linarith only [h0, h2808, h2898, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2927 | h2927
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2928 | h2928
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2929 | h2929
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2930 | h2930
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2931 | h2931
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2932 | h2932
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2933 | h2933
                        · linarith only [h2808, h2811, h2933, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2935 | h2935
                          · linarith only [h2494, h2808, h2869, h2935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2937 | h2937
                            · linarith only [h2809, h2897, h2937, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2939 | h2939
                              · linarith only [h1991, h2897, h2927, h2930, h2939, hc01, hc12, hlam, hphi]
                              · linarith only [h1106, h2811, h2927, h2930, h2932, h2939, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2942 | h2942
                        · linarith only [h1106, h2808, h2811, h2942, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2944 | h2944
                          · linarith only [h2808, h2869, h2944, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2946 | h2946
                            · linarith only [h2809, h2932, h2946, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2948 | h2948
                              · linarith only [h1991, h2897, h2927, h2930, h2948, hc01, hc12, hlam, hphi]
                              · rcases h2bigk with h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c | h2950c
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h0, hlam, p2950_1]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2950_1, u0elo1]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p2950_1, u0elo1]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht0b, ht5b, p2950_1, u0elo1]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  rcases p2950_3 (m.d 0 2) (by simp) with h2956 | h2956
                                  · linarith only [h0, h2956, hlam]
                                  · rcases p2950_3 (m.d 1 2) (by simp) with h2958 | h2958
                                    · rcases p2950_3 (m.d 2 3) (by simp) with h2959 | h2959
                                      · linarith only [h2927, h2959, hlam]
                                      · rcases p2950_3 (m.d 2 4) (by simp) with h2961 | h2961
                                        · linarith only [h2928, h2961, hlam]
                                        · rcases p2950_3 (m.d 2 5) (by simp) with h2963 | h2963
                                          · linarith only [h2929, h2963, hlam]
                                          · rcases h3bigk with h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c | h2965c
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h1106, hlam, p2965_1]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2965_1, u0elo2]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h2811, hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h2869, hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              rcases p2965_3 (m.d 0 3) (by simp) with h2971 | h2971
                                              · linarith only [h1106, h2971, hlam]
                                              · rcases p2965_3 (m.d 1 3) (by simp) with h2973 | h2973
                                                · rcases p2965_3 (m.d 2 3) (by simp) with h2974 | h2974
                                                  · linarith only [h2927, h2974, hlam]
                                                  · rcases p2965_3 (m.d 3 4) (by simp) with h2976 | h2976
                                                    · linarith only [h2930, h2976, hlam]
                                                    · linarith only [h2811, h2976, hlam]
                                                · linarith only [h1106, h2973, hlam]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              rcases p2965_3 (m.d 0 3) (by simp) with h2981 | h2981
                                              · linarith only [h1106, h2981, hlam]
                                              · linarith only [h2808, h2981, hlam]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h1106, h2811, hc01, hc13, hlam, hphi, p2965_1]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h1106, h2811, h2927, h2948, hc01, hc12, hlam, hphi, p2965_1]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h2808, hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h2927, hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h2942, hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h2944, hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h1106, h2930, h2932, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2965_1]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h2930, hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h2930, h2932, hc23, hc45, hlam, hphi, ht34, p2965_1]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h2948, hlam, p2965_1]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h1106, h2927, h2931, hc01, hc12, hlam, hphi, p2965_1]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h2931, hlam, p2965_0]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              rcases p2965_3 (m.d 0 3) (by simp) with h2998 | h2998
                                              · linarith only [h2869, h2998, hlam]
                                              · linarith only [h2808, h2998, hlam]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [h1106, h2811, h2931, hc01, hc15, hlam, hphi, p2965_1]
                                            · have p2965_0 := h2965c.1
                                              have p2965_1 := h2965c.2.1
                                              have p2965_2 := h2965c.2.2.1
                                              have p2965_3 := h2965c.2.2.2
                                              linarith only [hlam, p2965_0]
                                    · linarith only [h0, h2958, hlam]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  rcases p2950_3 (m.d 0 2) (by simp) with h3005 | h3005
                                  · linarith only [h0, h3005, hlam]
                                  · linarith only [h2808, h3005, hlam]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  rcases p2950_3 (m.d 0 2) (by simp) with h3008 | h3008
                                  · linarith only [h0, h3008, hlam]
                                  · linarith only [h2809, h3008, hlam]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  rcases p2950_3 (m.d 0 2) (by simp) with h3011 | h3011
                                  · linarith only [h0, h3011, hlam]
                                  · linarith only [h2810, h3011, hlam]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2808, hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2927, hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2942, hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2944, hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2809, hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2928, hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2810, h2946, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2950_1, u0elo1]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2946, hlam, p2950_1]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2810, hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2929, hlam, p2950_0]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2810, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2950_1, u0elo1]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [h2810, hc24, hlam, hphi, ht0b, ht45, ht5b, p2950_1, u0elo1]
                                · have p2950_0 := h2950c.1
                                  have p2950_1 := h2950c.2.1
                                  have p2950_2 := h2950c.2.2.1
                                  have p2950_3 := h2950c.2.2.2
                                  linarith only [hlam, p2950_0]
                    · linarith only [h1106, h2811, h2930, h2931, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3030 | h3030
                    · linarith only [h1106, h2869, h2930, h3030, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3032 | h3032
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3033 | h3033
                        · linarith only [h1106, h2930, h3033, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3035 | h3035
                          · linarith only [h2808, h3030, h3035, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3037 | h3037
                            · linarith only [h2809, h2897, h3037, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3039 | h3039
                              · rcases h2bigk with h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h0, hlam, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3040_1, u0elo1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p3040_1, u0elo1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht0b, ht5b, p3040_1, u0elo1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  rcases p3040_3 (m.d 0 2) (by simp) with h3046 | h3046
                                  · linarith only [h0, h3046, hlam]
                                  · rcases p3040_3 (m.d 1 2) (by simp) with h3048 | h3048
                                    · rcases p3040_3 (m.d 2 3) (by simp) with h3049 | h3049
                                      · linarith only [h2927, h3049, hlam]
                                      · rcases p3040_3 (m.d 2 4) (by simp) with h3051 | h3051
                                        · linarith only [h2928, h3051, hlam]
                                        · rcases p3040_3 (m.d 2 5) (by simp) with h3053 | h3053
                                          · linarith only [h2929, h3053, hlam]
                                          · rcases h3bigk with h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h1106, hlam, p3055_1]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3055_1, u0elo2]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h2811, hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h2869, hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h3030, hc03, hc35, hlam, hphi, p3055_1]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h3030, hc23, hc35, hlam, hphi, p3055_1]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h2930, hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h3030, hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h2808, hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h2927, hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h3033, hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h3035, hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              rcases p3055_3 (m.d 0 3) (by simp) with h3071 | h3071
                                              · linarith only [h3071, hlam, p3055_0]
                                              · rcases p3055_3 (m.d 1 3) (by simp) with h3073 | h3073
                                                · linarith only [h2930, h3073, hlam]
                                                · linarith only [h1106, h3073, hlam]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h1106, h2810, h3033, h3037, hc01, hc12, hc23, hc34, hlam, hphi, p3040_1, p3055_1]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              rcases p3055_3 (m.d 0 3) (by simp) with h3077 | h3077
                                              · linarith only [h2811, h3077, hlam]
                                              · linarith only [h2808, h3077, hlam]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h1106, h2810, h2869, h3033, h3037, hc01, hc12, hc23, hc34, hlam, hphi, p3040_1, p3055_1]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              rcases p3055_3 (m.d 0 3) (by simp) with h3082 | h3082
                                              · linarith only [h3082, hlam, p3055_0]
                                              · rcases p3055_3 (m.d 1 3) (by simp) with h3084 | h3084
                                                · linarith only [h3030, h3084, hlam]
                                                · linarith only [h1106, h3084, hlam]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h1106, h2810, h3033, h3037, hc01, hc12, hc23, hc35, hlam, hphi, p3040_1, p3055_1]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              rcases p3055_3 (m.d 0 3) (by simp) with h3088 | h3088
                                              · linarith only [h2869, h3088, hlam]
                                              · linarith only [h2808, h3088, hlam]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [h3039, hlam, p3055_0]
                                            · have p3055_0 := h3055c.1
                                              have p3055_1 := h3055c.2.1
                                              have p3055_2 := h3055c.2.2.1
                                              have p3055_3 := h3055c.2.2.2
                                              linarith only [hlam, p3055_0]
                                    · linarith only [h0, h3048, hlam]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  rcases p3040_3 (m.d 0 2) (by simp) with h3095 | h3095
                                  · linarith only [h0, h3095, hlam]
                                  · linarith only [h2808, h3095, hlam]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  rcases p3040_3 (m.d 0 2) (by simp) with h3098 | h3098
                                  · linarith only [h0, h3098, hlam]
                                  · linarith only [h2809, h3098, hlam]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  rcases p3040_3 (m.d 0 2) (by simp) with h3101 | h3101
                                  · linarith only [h0, h3101, hlam]
                                  · linarith only [h2810, h3101, hlam]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2808, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2927, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3033, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3035, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2809, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2928, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2810, h3037, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3040_1, u0elo1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h3037, hlam, p3040_1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2810, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2929, hlam, p3040_0]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2810, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3040_1, u0elo1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [h2810, hc24, hlam, hphi, ht0b, ht45, ht5b, p3040_1, u0elo1]
                                · have p3040_0 := h3040c.1
                                  have p3040_1 := h3040c.2.1
                                  have p3040_2 := h3040c.2.2.1
                                  have p3040_3 := h3040c.2.2.2
                                  linarith only [hlam, p3040_0]
                              · linarith only [h2930, h3032, h3039, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3120 | h3120
                        · linarith only [h2808, h3120, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3122 | h3122
                          · linarith only [h2808, h3122, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3124 | h3124
                            · linarith only [h1106, h2809, h2930, h3032, h3124, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3126 | h3126
                              · linarith only [h1106, h2930, h3032, h3126, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h1106, h2930, h3126, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h2810, h2929, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h2809, h2928, hlam]
            · linarith only [h0, h2808, h2809, h2927, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3132 | h3132
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3133 | h3133
        · linarith only [h2808, h2810, h3133, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3135 | h3135
          · linarith only [h2808, h2810, h3132, h3135, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3137 | h3137
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3138 | h3138
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3139 | h3139
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3140 | h3140
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3141 | h3141
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3142 | h3142
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3143 | h3143
                        · linarith only [h2808, h3143, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h2808, h2810, h3132, h3143, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3146 | h3146
                        · linarith only [h2808, h2810, h3146, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h2808, h2810, h3132, h3146, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3149 | h3149
                      · linarith only [h1991, h3135, h3140, h3141, h3149, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3151 | h3151
                        · linarith only [h2808, h2810, h3151, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h2808, h2810, h3132, h3151, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h1106, h2808, h2810, h3132, h3140, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3155 | h3155
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3156 | h3156
                    · linarith only [h3132, h3133, h3137, h3139, h3156, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3158 | h3158
                      · linarith only [h1991, h3135, h3138, h3139, h3158, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3160 | h3160
                        · linarith only [h2808, h2810, h3160, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h3132, h3160, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h2808, h2810, h3132, h3155, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
              · linarith only [h2809, h2810, h3138, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · linarith only [h0, h2808, h2810, h3137, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3166 | h3166
        · linarith only [h2809, h2810, h3132, h3166, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3168 | h3168
          · linarith only [h2809, h2810, h3168, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3170 | h3170
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3171 | h3171
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3172 | h3172
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3173 | h3173
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3174 | h3174
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3175 | h3175
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3176 | h3176
                        · linarith only [h2808, h3132, h3176, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3178 | h3178
                          · linarith only [h1106, h2809, h2810, h3166, h3176, h3178, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3180 | h3180
                            · linarith only [h2809, h2810, h3170, h3174, h3178, h3180, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3182 | h3182
                              · linarith only [h2809, h2810, h3176, h3180, h3182, hc23, hc34, hlam, hphi]
                              · linarith only [h1106, h3132, h3170, h3173, h3175, h3182, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3185 | h3185
                        · linarith only [h1106, h2808, h3132, h3185, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3187 | h3187
                          · linarith only [h2809, h2810, h3185, h3187, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3189 | h3189
                            · linarith only [h2809, h2810, h3170, h3174, h3175, h3187, h3189, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3191 | h3191
                              · linarith only [h3173, h3175, h3191, hlam]
                              · rcases h2bigk with h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c | h3193c
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h0, hlam, p3193_1]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h2810, h3170, h3174, h3187, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3193_1]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h2810, h3170, h3174, h3187, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3193_1]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h2810, hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  rcases p3193_3 (m.d 0 2) (by simp) with h3199 | h3199
                                  · linarith only [h0, h3199, hlam]
                                  · rcases p3193_3 (m.d 1 2) (by simp) with h3201 | h3201
                                    · rcases p3193_3 (m.d 2 3) (by simp) with h3202 | h3202
                                      · linarith only [h3170, h3202, hlam]
                                      · rcases p3193_3 (m.d 2 4) (by simp) with h3204 | h3204
                                        · linarith only [h3171, h3204, hlam]
                                        · rcases p3193_3 (m.d 2 5) (by simp) with h3206 | h3206
                                          · linarith only [h3172, h3206, hlam]
                                          · linarith only [h2810, h3206, hlam]
                                    · linarith only [h0, h3201, hlam]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h2808, h2810, h3170, h3174, h3187, hlam, p3193_2]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h2809, h2810, h3170, h3174, h3187, hlam, p3193_2]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h2809, h2810, h3185, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3193_1]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h2808, hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h3170, hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h3185, hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h3187, hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h2809, hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h3171, hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h2809, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3193_1, u0elo1]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h3189, hlam, p3193_1]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h2809, h3172, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3193_1]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [h3172, hlam, p3193_0]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  rcases p3193_3 (m.d 0 2) (by simp) with h3226 | h3226
                                  · linarith only [h2810, h3226, hlam]
                                  · linarith only [h2808, h3226, hlam]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  rcases p3193_3 (m.d 0 2) (by simp) with h3229 | h3229
                                  · linarith only [h2810, h3229, hlam]
                                  · linarith only [h2809, h3229, hlam]
                                · have p3193_0 := h3193c.1
                                  have p3193_1 := h3193c.2.1
                                  have p3193_2 := h3193c.2.2.1
                                  have p3193_3 := h3193c.2.2.2
                                  linarith only [hlam, p3193_0]
                    · linarith only [h1106, h3132, h3173, h3174, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3234 | h3234
                    · linarith only [h1106, h3166, h3173, h3234, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3236 | h3236
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3237 | h3237
                        · linarith only [h2808, h3173, h3237, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3239 | h3239
                          · linarith only [h2809, h2810, h3172, h3234, h3237, h3239, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3241 | h3241
                            · linarith only [h1106, h2809, h2810, h3132, h3168, h3172, h3241, hc01, hc12, hlam, hphi]
                            · linarith only [h2809, h2810, h3173, h3236, h3237, h3241, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3244 | h3244
                        · linarith only [h2808, h3244, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3246 | h3246
                          · linarith only [h2809, h2810, h3172, h3234, h3244, h3246, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3248 | h3248
                            · linarith only [h2809, h2810, h3172, h3236, h3248, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3250 | h3250
                              · linarith only [h1106, h3173, h3236, h3250, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h1106, h3173, h3250, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3253 | h3253
                  · linarith only [h1106, h3132, h3170, h3172, h3253, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3255 | h3255
                    · linarith only [h1106, h3166, h3171, h3172, h3253, h3255, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3257 | h3257
                      · linarith only [h1106, h3132, h3168, h3171, h3172, h3257, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3259 | h3259
                        · linarith only [h1106, h3253, h3259, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3261 | h3261
                          · linarith only [h2809, h3255, h3259, h3261, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3263 | h3263
                            · linarith only [h2809, h2810, h3263, hc45, hlam, hphi, ht0b, ht5b, u0elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3265 | h3265
                              · linarith only [h2809, h2810, h3259, h3263, h3265, hc23, hc34, hlam, hphi]
                              · linarith only [h1106, h3253, h3265, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h1106, h2809, h2810, h3170, h3171, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
            · linarith only [h0, h2808, h3170, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3270 | h3270
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3271 | h3271
      · linarith only [h2808, h2809, h3271, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3273 | h3273
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3274 | h3274
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3275 | h3275
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3276 | h3276
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3277 | h3277
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3278 | h3278
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3279 | h3279
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3280 | h3280
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3281 | h3281
                        · linarith only [h2808, h2809, h3271, h3276, h3281, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3283 | h3283
                          · linarith only [h2808, h2809, h3275, h3278, h3281, h3283, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h3273, h3283, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h2809, h3274, h3276, h3280, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h3271, h3273, h3278, h3279, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3288 | h3288
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3289 | h3289
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3290 | h3290
                        · linarith only [h2808, h3278, h3290, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3292 | h3292
                          · linarith only [h2808, h2809, h3276, h3292, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h3273, h3292, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h3274, h3289, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h2808, h2809, h3273, h3276, h3288, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h2809, h3276, h3277, hc02, hc25, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3298 | h3298
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3299 | h3299
                  · linarith only [h3271, h3273, h3275, h3276, h3299, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3301 | h3301
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3302 | h3302
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3303 | h3303
                        · linarith only [h2808, h3299, h3303, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3305 | h3305
                          · linarith only [h2808, h2809, h3305, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h3273, h3305, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h3274, h3276, h3302, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1106, h3273, h3301, hlam]
                · linarith only [h0, h3270, h3298, hlam]
            · linarith only [h0, h2808, h3275, hlam]
          · linarith only [h2808, h2809, h3273, h3274, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3313 | h3313
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3314 | h3314
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3315 | h3315
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3316 | h3316
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3317 | h3317
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3318 | h3318
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3319 | h3319
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3320 | h3320
                        · linarith only [h1106, h2808, h2809, h3271, h3315, h3320, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3322 | h3322
                          · linarith only [h1106, h2808, h2809, h3273, h3314, h3317, h3320, h3322, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3324 | h3324
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3325 | h3325
                              · rcases h2bigk with h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h0, hlam, p3326_1]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h2809, h3314, h3317, h3320, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3326_1]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h2809, hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h2809, h3314, h3317, h3320, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3326_1]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  rcases p3326_3 (m.d 0 2) (by simp) with h3332 | h3332
                                  · linarith only [h0, h3332, hlam]
                                  · rcases p3326_3 (m.d 1 2) (by simp) with h3334 | h3334
                                    · rcases p3326_3 (m.d 2 3) (by simp) with h3335 | h3335
                                      · linarith only [h3314, h3335, hlam]
                                      · rcases p3326_3 (m.d 2 4) (by simp) with h3337 | h3337
                                        · linarith only [h3315, h3337, hlam]
                                        · linarith only [h2809, h3337, hlam]
                                    · linarith only [h0, h3334, hlam]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h2808, h2809, h3314, h3317, h3320, hlam, p3326_2]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h2809, h3270, h3322, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3326_1]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h2809, h3270, h3315, hlam, p3326_2]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h2808, hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h3314, hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h3320, hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h3322, hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h3270, h3315, h3322, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3326_1]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h3315, hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  rcases p3326_3 (m.d 0 2) (by simp) with h3352 | h3352
                                  · linarith only [h2809, h3352, hlam]
                                  · linarith only [h2808, h3352, hlam]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  rcases p3326_3 (m.d 0 2) (by simp) with h3356 | h3356
                                  · linarith only [h2809, h3356, hlam]
                                  · linarith only [h3270, h3356, hlam]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h3270, hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h3316, hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h3270, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3326_1, u0elo1]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [h3324, hlam, p3326_0]
                                · have p3326_0 := h3326c.1
                                  have p3326_1 := h3326c.2.1
                                  have p3326_2 := h3326c.2.2.1
                                  have p3326_3 := h3326c.2.2.2
                                  linarith only [hlam, p3326_0]
                              · linarith only [h2808, h2809, h3320, h3325, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h2809, h3270, h3313, h3322, h3324, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h2808, h2809, h3313, h3315, h3319, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1106, h3271, h3317, h3318, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3368 | h3368
                    · linarith only [h1106, h3273, h3317, h3368, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3370 | h3370
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3371 | h3371
                        · linarith only [h2808, h3317, h3371, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3373 | h3373
                          · linarith only [h1106, h2808, h2809, h3315, h3368, h3373, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3375 | h3375
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3376 | h3376
                              · rcases h2bigk with h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c | h3377c
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h0, hlam, p3377_1]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h2809, h3315, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3377_1]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h2809, hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h2809, h3315, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3377_1]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  rcases p3377_3 (m.d 0 2) (by simp) with h3383 | h3383
                                  · linarith only [h0, h3383, hlam]
                                  · rcases p3377_3 (m.d 1 2) (by simp) with h3385 | h3385
                                    · rcases p3377_3 (m.d 2 3) (by simp) with h3386 | h3386
                                      · linarith only [h3314, h3386, hlam]
                                      · rcases p3377_3 (m.d 2 4) (by simp) with h3388 | h3388
                                        · linarith only [h3315, h3388, hlam]
                                        · linarith only [h2809, h3388, hlam]
                                    · linarith only [h0, h3385, hlam]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h2808, h2809, h3315, hlam, p3377_2]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h0, h2809, hc01, hc12, hlam, hphi, p3377_1]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h2809, h3270, h3315, hlam, p3377_2]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h2808, hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h3314, hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h3371, hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h3373, hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h3270, h3315, h3317, h3373, hc23, hc34, hlam, hphi, p3377_1]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h3315, hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  rcases p3377_3 (m.d 0 2) (by simp) with h3403 | h3403
                                  · linarith only [h2809, h3403, hlam]
                                  · linarith only [h2808, h3403, hlam]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  rcases p3377_3 (m.d 0 2) (by simp) with h3407 | h3407
                                  · linarith only [h2809, h3407, hlam]
                                  · linarith only [h3270, h3407, hlam]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h3270, hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h3316, hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h3270, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3377_1, u0elo1]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [h3375, hlam, p3377_0]
                                · have p3377_0 := h3377c.1
                                  have p3377_1 := h3377c.2.1
                                  have p3377_2 := h3377c.2.2.1
                                  have p3377_3 := h3377c.2.2.2
                                  linarith only [hlam, p3377_0]
                              · linarith only [h3313, h3317, h3376, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                            · linarith only [h2809, h3270, h3313, h3373, h3375, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h2809, h3313, h3315, h3370, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h3270, h3316, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3419 | h3419
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3420 | h3420
                  · linarith only [h1106, h3271, h3314, h3315, h3420, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3422 | h3422
                    · linarith only [h1106, h3273, h3314, h3315, h3422, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3424 | h3424
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3425 | h3425
                        · linarith only [h1106, h3420, h3425, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3427 | h3427
                          · linarith only [h1106, h2808, h2809, h3422, h3427, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3429 | h3429
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3430 | h3430
                              · rcases h2bigk with h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c | h3431c
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h0, hlam, p3431_1]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h2809, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3431_1, u0elo3]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h2809, hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h2809, hc25, hlam, hphi, ht0b, ht5b, p3431_1, u0elo3]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h3315, h3425, hc02, hc34, hlam, hphi, ht23, p3431_1]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h3315, h3425, hc23, hc34, hlam, hphi, p3431_1]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h3315, hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h3315, h3425, h3427, hc23, hc34, hlam, hphi, p3431_1]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h2808, hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h3314, hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h3425, hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h3427, hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h2808, h3425, hc23, hc34, hlam, hphi, p3431_1]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h0, h3425, hc01, hc34, hlam, hphi, ht12, ht23, p3431_1]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  rcases p3431_3 (m.d 0 2) (by simp) with h3449 | h3449
                                  · linarith only [h2809, h3449, hlam]
                                  · linarith only [h2808, h3449, hlam]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  rcases p3431_3 (m.d 0 2) (by simp) with h3453 | h3453
                                  · linarith only [h2809, h3453, hlam]
                                  · linarith only [h3270, h3453, hlam]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h3270, hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h3419, hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h3270, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3431_1, u0elo1]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [h3429, hlam, p3431_0]
                                · have p3431_0 := h3431c.1
                                  have p3431_1 := h3431c.2.1
                                  have p3431_2 := h3431c.2.2.1
                                  have p3431_3 := h3431c.2.2.2
                                  linarith only [hlam, p3431_0]
                              · linarith only [h2808, h2809, h3425, h3430, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h1106, h3313, h3315, h3419, h3422, h3429, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h3313, h3424, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h0, h3270, h3419, hlam]
            · linarith only [h0, h2808, h3314, hlam]
          · linarith only [h2809, h3270, h3313, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3467 | h3467
      · linarith only [h2808, h2809, h3467, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3469 | h3469
        · linarith only [h2808, h3270, h3469, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3471 | h3471
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3472 | h3472
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3473 | h3473
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3474 | h3474
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3475 | h3475
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3476 | h3476
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3477 | h3477
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3478 | h3478
                        · linarith only [h1106, h2808, h3467, h3478, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3480 | h3480
                          · linarith only [h1106, h2808, h2809, h3469, h3472, h3475, h3478, h3480, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3482 | h3482
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3483 | h3483
                              · rcases h2bigk with h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h0, hlam, p3484_1]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h3270, h3472, h3475, h3478, h3482, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3484_1]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h2809, hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h3270, hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  rcases p3484_3 (m.d 0 2) (by simp) with h3490 | h3490
                                  · linarith only [h0, h3490, hlam]
                                  · rcases p3484_3 (m.d 1 2) (by simp) with h3492 | h3492
                                    · rcases p3484_3 (m.d 2 3) (by simp) with h3493 | h3493
                                      · linarith only [h3472, h3493, hlam]
                                      · rcases p3484_3 (m.d 2 4) (by simp) with h3495 | h3495
                                        · linarith only [h3473, h3495, hlam]
                                        · linarith only [h2809, h3495, hlam]
                                    · linarith only [h0, h3492, hlam]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h2808, h3270, h3472, h3475, h3478, h3482, hlam, p3484_2]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h2808, h3270, h3482, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3484_1]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h2808, h3270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3484_1]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h2808, hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h3472, hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h3478, hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h3480, hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h2808, h3478, hc23, hc34, hlam, hphi, p3484_1]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h3473, hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  rcases p3484_3 (m.d 0 2) (by simp) with h3510 | h3510
                                  · linarith only [h2809, h3510, hlam]
                                  · linarith only [h2808, h3510, hlam]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h2808, h3270, h3475, h3478, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3484_1]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h2808, h3480, hc23, hc35, hlam, hphi, p3484_1]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h3474, hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  rcases p3484_3 (m.d 0 2) (by simp) with h3517 | h3517
                                  · linarith only [h3270, h3517, hlam]
                                  · linarith only [h2808, h3517, hlam]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [h3482, hlam, p3484_0]
                                · have p3484_0 := h3484c.1
                                  have p3484_1 := h3484c.2.1
                                  have p3484_2 := h3484c.2.2.1
                                  have p3484_3 := h3484c.2.2.2
                                  linarith only [hlam, p3484_0]
                              · linarith only [h3471, h3478, h3483, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                            · linarith only [h2808, h2809, h3471, h3482, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h3471, h3477, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h1106, h3467, h3475, h3476, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3526 | h3526
                    · linarith only [h1106, h3469, h3475, h3526, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3528 | h3528
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3529 | h3529
                        · linarith only [h2808, h3475, h3529, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3531 | h3531
                          · linarith only [h2808, h3270, h3474, h3526, h3531, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3533 | h3533
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3534 | h3534
                              · rcases h2bigk with h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h0, hlam, p3535_1]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h3270, h3471, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3535_1, u0elo3]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h2809, hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h3270, hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  rcases p3535_3 (m.d 0 2) (by simp) with h3541 | h3541
                                  · linarith only [h0, h3541, hlam]
                                  · rcases p3535_3 (m.d 1 2) (by simp) with h3543 | h3543
                                    · rcases p3535_3 (m.d 2 3) (by simp) with h3544 | h3544
                                      · linarith only [h3472, h3544, hlam]
                                      · rcases p3535_3 (m.d 2 4) (by simp) with h3546 | h3546
                                        · linarith only [h3473, h3546, hlam]
                                        · linarith only [h2809, h3546, hlam]
                                    · linarith only [h0, h3543, hlam]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h2808, h3270, h3473, h3533, hlam, p3535_2]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h0, h3270, h3533, hc01, hc12, hlam, hphi, p3535_1]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h2808, h3270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3535_1]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h2808, hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h3472, hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h3529, hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h3531, hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h2808, h3473, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3535_1]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h3473, hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  rcases p3535_3 (m.d 0 2) (by simp) with h3561 | h3561
                                  · linarith only [h2809, h3561, hlam]
                                  · linarith only [h2808, h3561, hlam]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h2808, h3270, h3473, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3535_1]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h2808, h3474, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3535_1]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h3474, hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  rcases p3535_3 (m.d 0 2) (by simp) with h3568 | h3568
                                  · linarith only [h3270, h3568, hlam]
                                  · linarith only [h2808, h3568, hlam]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [h3533, hlam, p3535_0]
                                · have p3535_0 := h3535c.1
                                  have p3535_1 := h3535c.2.1
                                  have p3535_2 := h3535c.2.2.1
                                  have p3535_3 := h3535c.2.2.2
                                  linarith only [hlam, p3535_0]
                              · linarith only [h1991, h3471, h3475, h3534, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h3471, h3533, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h3471, h3528, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h2808, h2809, h3473, h3474, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3577 | h3577
                · linarith only [h2808, h3270, h3473, h3577, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3579 | h3579
                  · linarith only [h1106, h3467, h3472, h3473, h3579, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3581 | h3581
                    · linarith only [h1106, h3469, h3579, h3581, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3583 | h3583
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3584 | h3584
                        · linarith only [h2808, h3579, h3584, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3586 | h3586
                          · linarith only [h1106, h2808, h3581, h3586, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3588 | h3588
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3589 | h3589
                              · rcases h2bigk with h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h0, hlam, p3590_1]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3270, h3471, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3590_1, u0elo3]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h2809, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3270, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3577, h3584, h3588, hc02, hc34, hlam, hphi, ht23, p3590_1]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3577, h3584, h3588, hc23, hc34, hlam, hphi, p3590_1]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3473, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3577, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h2808, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3472, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3584, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3586, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h2808, h3584, hc23, hc34, hlam, hphi, p3590_1]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h0, h3584, hc01, hc34, hlam, hphi, ht12, ht23, p3590_1]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  rcases p3590_3 (m.d 0 2) (by simp) with h3608 | h3608
                                  · linarith only [h2809, h3608, hlam]
                                  · linarith only [h2808, h3608, hlam]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h2808, h3270, h3584, hc23, hc34, hlam, hphi, p3590_1]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h2808, h3586, hc23, hc35, hlam, hphi, p3590_1]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h1106, h3472, h3586, hc01, hc35, hlam, hphi, ht12, ht23, p3590_1]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  rcases p3590_3 (m.d 0 2) (by simp) with h3615 | h3615
                                  · linarith only [h3270, h3615, hlam]
                                  · linarith only [h2808, h3615, hlam]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3588, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [hlam, p3590_0]
                              · linarith only [h3471, h3584, h3589, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                            · linarith only [h1106, h3471, h3472, h3473, h3588, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h1991, h3471, h3583, hlam]
            · linarith only [h2808, h3472, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3624 | h3624
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3625 | h3625
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3626 | h3626
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3627 | h3627
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3628 | h3628
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3629 | h3629
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3630 | h3630
                        · linarith only [h1106, h2808, h2809, h3467, h3471, h3624, h3627, h3629, h3630, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3632 | h3632
                          · linarith only [h2808, h2809, h3471, h3624, h3627, h3629, h3632, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3634 | h3634
                            · linarith only [h2808, h2809, h3471, h3624, h3627, h3630, h3634, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h2808, h2809, h3634, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h2808, h2809, h3625, h3629, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1106, h3467, h3627, h3628, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3639 | h3639
                    · linarith only [h1106, h3469, h3627, h3639, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3641 | h3641
                      · linarith only [h2808, h2809, h3471, h3627, h3641, hc23, hc34, hlam, hphi]
                      · linarith only [h2808, h2809, h3625, h3641, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h2808, h2809, h3625, h3626, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3645 | h3645
                · linarith only [h2808, h3270, h3625, h3645, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3647 | h3647
                  · linarith only [h1106, h3467, h3624, h3625, h3647, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3649 | h3649
                    · linarith only [h1106, h3469, h3647, h3649, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3651 | h3651
                      · linarith only [h2808, h2809, h3471, h3647, h3651, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3653 | h3653
                        · linarith only [h2808, h3653, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3655 | h3655
                          · linarith only [h2808, h2809, h3471, h3649, h3655, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3657 | h3657
                            · linarith only [h0, h3625, h3651, h3653, h3657, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h2808, h2809, h3657, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h2808, h3624, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]

end R2N4
