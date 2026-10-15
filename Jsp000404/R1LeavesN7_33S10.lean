import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_33S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x1_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2314 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2315 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2870 | h2870
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2871 | h2871
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2872 | h2872
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2873 | h2873
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2874 | h2874
          · linarith only [h2314, h2315, h2874, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2876 | h2876
            · linarith only [h2314, h2315, h2873, h2876, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2878 | h2878
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2879 | h2879
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2880 | h2880
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2881 | h2881
                    · linarith only [h2314, h2315, h2880, h2881, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h2314, h2315, h2873, h2878, h2880, h2881, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h2872, h2880, hc12, hlam, hphi, u2elo0]
                · linarith only [h0, h2314, h2878, h2879, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2314, h2878, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2887 | h2887
          · linarith only [h2314, h2315, h2887, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2889 | h2889
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2890 | h2890
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2891 | h2891
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2892 | h2892
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2893 | h2893
                    · linarith only [h2314, h2315, h2873, h2892, h2893, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2895 | h2895
                      · linarith only [h2314, h2315, h2887, h2892, h2895, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2897 | h2897
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2898 | h2898
                          · linarith only [h2315, h2893, h2897, h2898, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2900 | h2900
                            · linarith only [h2314, h2315, h2890, h2895, h2900, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2902 | h2902
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2903 | h2903
                                · rcases h2bigk with h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h0, hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    rcases p2904_3 (m.d 0 2) (by simp) with h2907 | h2907
                                    · rcases p2904_3 (m.d 1 2) (by simp) with h2908 | h2908
                                      · rcases p2904_3 (m.d 2 3) (by simp) with h2909 | h2909
                                        · linarith only [h2909, hlam, p2904_0]
                                        · rcases p2904_3 (m.d 2 4) (by simp) with h2911 | h2911
                                          · linarith only [h2871, h2911, hlam]
                                          · linarith only [h2898, h2911, hlam]
                                      · linarith only [h2890, h2908, hlam]
                                    · linarith only [h2907, hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2902, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2904_1, u2elo0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    rcases p2904_3 (m.d 0 2) (by simp) with h2917 | h2917
                                    · rcases p2904_3 (m.d 1 2) (by simp) with h2918 | h2918
                                      · rcases p2904_3 (m.d 2 3) (by simp) with h2919 | h2919
                                        · linarith only [h2870, h2919, hlam]
                                        · rcases p2904_3 (m.d 2 4) (by simp) with h2921 | h2921
                                          · linarith only [h2871, h2921, hlam]
                                          · linarith only [h2902, h2921, hlam]
                                      · linarith only [h2892, h2918, hlam]
                                    · linarith only [h2917, hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2904_1, u2elo1]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    rcases p2904_3 (m.d 0 2) (by simp) with h2928 | h2928
                                    · linarith only [h0, h2928, hlam]
                                    · linarith only [h2870, h2928, hlam]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2902, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2904_1, u2elo1]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    rcases p2904_3 (m.d 0 2) (by simp) with h2932 | h2932
                                    · linarith only [h0, h2932, hlam]
                                    · linarith only [h2872, h2932, hlam]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2870, hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2890, hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2898, hlam, p2904_1]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2900, hlam, p2904_1]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2871, hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2891, hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2871, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2904_1, u2elo0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h0, h2871, h2900, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2904_1, u2elo1]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2872, hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2892, hlam, p2904_0]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h0, h2872, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2904_1, u2elo1]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [h2902, hlam, p2904_1]
                                  · have p2904_0 := h2904c.1
                                    have p2904_1 := h2904c.2.1
                                    have p2904_2 := h2904c.2.2.1
                                    have p2904_3 := h2904c.2.2.2
                                    linarith only [hlam, p2904_0]
                                · linarith only [h2314, h2315, h2890, h2893, h2897, h2903, hc23, hc45, hlam, hphi, ht34]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2951 | h2951
                                · rcases h2bigk with h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h0, hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    rcases p2952_3 (m.d 0 2) (by simp) with h2955 | h2955
                                    · rcases p2952_3 (m.d 1 2) (by simp) with h2956 | h2956
                                      · rcases p2952_3 (m.d 2 3) (by simp) with h2957 | h2957
                                        · linarith only [h2957, hlam, p2952_0]
                                        · rcases p2952_3 (m.d 2 4) (by simp) with h2959 | h2959
                                          · linarith only [h2871, h2959, hlam]
                                          · linarith only [h2898, h2959, hlam]
                                      · linarith only [h2890, h2956, hlam]
                                    · linarith only [h2955, hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    rcases p2952_3 (m.d 0 2) (by simp) with h2964 | h2964
                                    · rcases p2952_3 (m.d 1 2) (by simp) with h2965 | h2965
                                      · rcases p2952_3 (m.d 2 3) (by simp) with h2966 | h2966
                                        · linarith only [h2870, h2966, hlam]
                                        · rcases p2952_3 (m.d 2 4) (by simp) with h2968 | h2968
                                          · linarith only [h2968, hlam, p2952_0]
                                          · rcases p2952_3 (m.d 2 5) (by simp) with h2970 | h2970
                                            · linarith only [h2872, h2970, hlam]
                                            · linarith only [h2902, h2970, hlam]
                                      · linarith only [h2891, h2965, hlam]
                                    · linarith only [h2964, hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    rcases p2952_3 (m.d 0 2) (by simp) with h2975 | h2975
                                    · rcases p2952_3 (m.d 1 2) (by simp) with h2976 | h2976
                                      · rcases p2952_3 (m.d 2 3) (by simp) with h2977 | h2977
                                        · linarith only [h2870, h2977, hlam]
                                        · rcases p2952_3 (m.d 2 4) (by simp) with h2979 | h2979
                                          · linarith only [h2871, h2979, hlam]
                                          · rcases p2952_3 (m.d 2 5) (by simp) with h2981 | h2981
                                            · linarith only [h2981, hlam, p2952_0]
                                            · rcases h3bigk with h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2314, h2315, h2890, h2893, h2897, hc23, hc34, hlam, hphi, p2983_1]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h0, h2314, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2983_1, u2elo1]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2873, hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2887, hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2314, hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h0, h2314, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2983_1, u2elo1]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2893, hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2895, hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2870, hlam, p2983_1]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2890, hlam, p2983_1]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2898, hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2900, hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                rcases p2983_3 (m.d 0 3) (by simp) with h2999 | h2999
                                                · linarith only [h2999, hlam, p2983_0]
                                                · rcases p2983_3 (m.d 1 3) (by simp) with h3001 | h3001
                                                  · linarith only [h2893, h3001, hlam]
                                                  · rcases p2983_3 (m.d 2 3) (by simp) with h3003 | h3003
                                                    · linarith only [h2898, h3003, hlam]
                                                    · rcases p2983_3 (m.d 3 4) (by simp) with h3005 | h3005
                                                      · rcases p2983_3 (m.d 3 5) (by simp) with h3006 | h3006
                                                        · linarith only [h2951, h3006, hlam]
                                                        · linarith only [h2887, h3006, hlam]
                                                      · linarith only [h3005, hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                rcases p2983_3 (m.d 0 3) (by simp) with h3010 | h3010
                                                · linarith only [h2873, h3010, hlam]
                                                · linarith only [h2314, h3010, hlam]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                rcases p2983_3 (m.d 0 3) (by simp) with h3013 | h3013
                                                · linarith only [h2873, h3013, hlam]
                                                · linarith only [h2870, h3013, hlam]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [hlam, p2983_0]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2315, h2895, hc01, hc34, hlam, hphi, ht12, ht23, p2983_1]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                rcases p2983_3 (m.d 0 3) (by simp) with h3018 | h3018
                                                · linarith only [h3018, hlam, p2983_0]
                                                · rcases p2983_3 (m.d 1 3) (by simp) with h3020 | h3020
                                                  · linarith only [h2895, h3020, hlam]
                                                  · rcases p2983_3 (m.d 2 3) (by simp) with h3022 | h3022
                                                    · linarith only [h2900, h3022, hlam]
                                                    · rcases p2983_3 (m.d 3 4) (by simp) with h3024 | h3024
                                                      · rcases p2983_3 (m.d 3 5) (by simp) with h3025 | h3025
                                                        · rcases h5bigk with h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [hlam, p3026_0]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2315, hlam, p3026_1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            rcases p3026_3 (m.d 0 5) (by simp) with h3029 | h3029
                                                            · rcases p3026_3 (m.d 1 5) (by simp) with h3030 | h3030
                                                              · rcases p3026_3 (m.d 2 5) (by simp) with h3031 | h3031
                                                                · linarith only [h2872, h3031, hlam]
                                                                · rcases p3026_3 (m.d 3 5) (by simp) with h3033 | h3033
                                                                  · rcases p3026_3 (m.d 4 5) (by simp) with h3034 | h3034
                                                                    · linarith only [h2889, h3034, hlam]
                                                                    · linarith only [h2902, h3034, hlam]
                                                                  · linarith only [h2900, h3033, hlam]
                                                              · linarith only [h2892, h3030, hlam]
                                                            · linarith only [h2872, h3029, hlam]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2887, hlam, p3026_0]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2315, h2891, h2897, h2898, h2902, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3026_1, u2elo1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2314, h2315, h2890, h2891, h2897, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3026_1, u2elo1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [hlam, p3026_0]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            rcases p3026_3 (m.d 0 5) (by simp) with h3044 | h3044
                                                            · linarith only [h2315, h3044, hlam]
                                                            · linarith only [h2872, h3044, hlam]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2895, hlam, p3026_0]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2891, h2897, h2898, h2902, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3026_1, u2elo1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2872, hlam, p3026_1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2892, hlam, p3026_1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [hlam, p3026_0]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2900, hlam, p3026_1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2902, hlam, p3026_0]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2314, h2315, h2890, h2951, hc23, hc34, hlam, hphi, p3026_1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2314, h2315, h2890, h2951, hc23, hc34, hlam, hphi, p3026_1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            rcases p3026_3 (m.d 0 5) (by simp) with h3056 | h3056
                                                            · linarith only [h2887, h3056, hlam]
                                                            · linarith only [h2872, h3056, hlam]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [hlam, p3026_0]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2898, h2902, h2951, hc23, hc34, hlam, hphi, p3026_1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2889, hlam, p3026_1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2897, hlam, p3026_1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h0, h2871, h2889, h2898, h2902, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3026_1, u2elo1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [h2951, hlam, p3026_1]
                                                          · have p3026_0 := h3026c.1
                                                            have p3026_1 := h3026c.2.1
                                                            have p3026_2 := h3026c.2.2.1
                                                            have p3026_3 := h3026c.2.2.2
                                                            linarith only [hlam, p3026_0]
                                                        · linarith only [h3025, hlam, p2983_0]
                                                      · linarith only [h2873, h3024, hlam]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                rcases p2983_3 (m.d 0 3) (by simp) with h3068 | h3068
                                                · linarith only [h2887, h3068, hlam]
                                                · linarith only [h2314, h3068, hlam]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                rcases p2983_3 (m.d 0 3) (by simp) with h3071 | h3071
                                                · linarith only [h2887, h3071, hlam]
                                                · linarith only [h2870, h3071, hlam]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [h2951, hlam, p2983_1]
                                              · have p2983_0 := h2983c.1
                                                have p2983_1 := h2983c.2.1
                                                have p2983_2 := h2983c.2.2.1
                                                have p2983_3 := h2983c.2.2.2
                                                linarith only [hlam, p2983_0]
                                      · linarith only [h2892, h2976, hlam]
                                    · linarith only [h2975, hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2952_1, u2elo1]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    rcases p2952_3 (m.d 0 2) (by simp) with h3080 | h3080
                                    · linarith only [h0, h3080, hlam]
                                    · linarith only [h2870, h3080, hlam]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    rcases p2952_3 (m.d 0 2) (by simp) with h3083 | h3083
                                    · linarith only [h0, h3083, hlam]
                                    · linarith only [h2871, h3083, hlam]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    rcases p2952_3 (m.d 0 2) (by simp) with h3086 | h3086
                                    · linarith only [h0, h3086, hlam]
                                    · linarith only [h2872, h3086, hlam]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h2870, hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h2890, hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h2898, hlam, p2952_1]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h2900, hlam, p2952_1]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h2871, hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h2891, hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h2871, h2889, h2902, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2952_1]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h2902, hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h2872, hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h2892, hlam, p2952_0]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h0, h2872, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2952_1, u2elo1]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [h0, h2871, h2889, h2902, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2952_1, u2elo1]
                                  · have p2952_0 := h2952c.1
                                    have p2952_1 := h2952c.2.1
                                    have p2952_2 := h2952c.2.2.1
                                    have p2952_3 := h2952c.2.2.2
                                    linarith only [hlam, p2952_0]
                                · linarith only [h0, h2314, h2871, h2873, h2889, h2890, h2951, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h2314, h2315, h2871, h2889, h2890, h2897, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2314, h2890, h2892, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h2314, h2890, h2891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2314, h2890, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3109 | h3109
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3110 | h3110
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3111 | h3111
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3112 | h3112
                    · linarith only [h2314, h2315, h3111, h3112, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3114 | h3114
                      · linarith only [h2314, h2315, h3111, h3114, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3116 | h3116
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3117 | h3117
                          · linarith only [h2314, h2873, h2889, h3109, h3112, h3116, h3117, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3119 | h3119
                            · linarith only [h2314, h2873, h2889, h3109, h3110, h3114, h3116, h3119, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3121 | h3121
                              · linarith only [h2871, h2889, h3121, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3123 | h3123
                                · rcases h2bigk with h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h0, hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    rcases p3124_3 (m.d 0 2) (by simp) with h3127 | h3127
                                    · rcases p3124_3 (m.d 1 2) (by simp) with h3128 | h3128
                                      · rcases p3124_3 (m.d 2 3) (by simp) with h3129 | h3129
                                        · linarith only [h3129, hlam, p3124_0]
                                        · rcases p3124_3 (m.d 2 4) (by simp) with h3131 | h3131
                                          · linarith only [h2871, h3131, hlam]
                                          · linarith only [h3117, h3131, hlam]
                                      · linarith only [h3109, h3128, hlam]
                                    · linarith only [h3127, hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    rcases p3124_3 (m.d 0 2) (by simp) with h3136 | h3136
                                    · rcases p3124_3 (m.d 1 2) (by simp) with h3137 | h3137
                                      · rcases p3124_3 (m.d 2 3) (by simp) with h3138 | h3138
                                        · linarith only [h2870, h3138, hlam]
                                        · rcases p3124_3 (m.d 2 4) (by simp) with h3140 | h3140
                                          · linarith only [h3140, hlam, p3124_0]
                                          · rcases p3124_3 (m.d 2 5) (by simp) with h3142 | h3142
                                            · linarith only [h2872, h3142, hlam]
                                            · linarith only [h3121, h3142, hlam]
                                      · linarith only [h3110, h3137, hlam]
                                    · linarith only [h3136, hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    rcases p3124_3 (m.d 0 2) (by simp) with h3147 | h3147
                                    · rcases p3124_3 (m.d 1 2) (by simp) with h3148 | h3148
                                      · rcases p3124_3 (m.d 2 3) (by simp) with h3149 | h3149
                                        · linarith only [h2870, h3149, hlam]
                                        · rcases p3124_3 (m.d 2 4) (by simp) with h3151 | h3151
                                          · linarith only [h2871, h3151, hlam]
                                          · rcases p3124_3 (m.d 2 5) (by simp) with h3153 | h3153
                                            · linarith only [h3153, hlam, p3124_0]
                                            · rcases h3bigk with h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c | h3155c
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h2873, h2889, h3109, h3110, h3116, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3155_1, u2elo1]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h2873, h2889, h3110, h3116, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3155_1, u2elo1]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h2873, hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h2887, hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h2314, hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h2314, h2315, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3155_1]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h3112, hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h3114, hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h2870, hlam, p3155_1]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h3109, hlam, p3155_1]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h3117, hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h3119, hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                rcases p3155_3 (m.d 0 3) (by simp) with h3171 | h3171
                                                · linarith only [h3171, hlam, p3155_0]
                                                · rcases p3155_3 (m.d 1 3) (by simp) with h3173 | h3173
                                                  · linarith only [h3112, h3173, hlam]
                                                  · rcases p3155_3 (m.d 2 3) (by simp) with h3175 | h3175
                                                    · linarith only [h3117, h3175, hlam]
                                                    · rcases p3155_3 (m.d 3 4) (by simp) with h3177 | h3177
                                                      · rcases p3155_3 (m.d 3 5) (by simp) with h3178 | h3178
                                                        · linarith only [h3123, h3178, hlam]
                                                        · linarith only [h2887, h3178, hlam]
                                                      · linarith only [h3177, hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                rcases p3155_3 (m.d 0 3) (by simp) with h3182 | h3182
                                                · linarith only [h2873, h3182, hlam]
                                                · linarith only [h2314, h3182, hlam]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                rcases p3155_3 (m.d 0 3) (by simp) with h3185 | h3185
                                                · linarith only [h2873, h3185, hlam]
                                                · linarith only [h2870, h3185, hlam]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [hlam, p3155_0]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h2314, h2887, h3109, hc23, hc34, hlam, hphi, p3155_1]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                rcases p3155_3 (m.d 0 3) (by simp) with h3190 | h3190
                                                · linarith only [h3190, hlam, p3155_0]
                                                · rcases p3155_3 (m.d 1 3) (by simp) with h3192 | h3192
                                                  · linarith only [h3114, h3192, hlam]
                                                  · rcases p3155_3 (m.d 2 3) (by simp) with h3194 | h3194
                                                    · linarith only [h3119, h3194, hlam]
                                                    · rcases p3155_3 (m.d 3 4) (by simp) with h3196 | h3196
                                                      · rcases p3155_3 (m.d 3 5) (by simp) with h3197 | h3197
                                                        · rcases h5bigk with h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c | h3198c
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [hlam, p3198_0]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h2315, hlam, p3198_1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h2889, h3110, h3116, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3198_1, u2elo1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h2887, hlam, p3198_0]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h2889, hlam, p3198_0]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h2315, h3110, h3116, hc01, hlam, hphi, ht12, p3198_1, u2elo1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [hlam, p3198_0]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            rcases p3198_3 (m.d 0 5) (by simp) with h3206 | h3206
                                                            · linarith only [h2315, h3206, hlam]
                                                            · linarith only [h2872, h3206, hlam]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h3114, hlam, p3198_0]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h2314, h2873, h2889, h3109, h3110, h3116, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3198_1, u2elo1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h2872, hlam, p3198_1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h3111, hlam, p3198_1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [hlam, p3198_0]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h3119, hlam, p3198_1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h3121, hlam, p3198_0]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h2314, h2315, h3109, hc23, hc35, hlam, hphi, p3198_1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h2314, h2315, h3109, hc23, hc35, hlam, hphi, p3198_1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            rcases p3198_3 (m.d 0 5) (by simp) with h3218 | h3218
                                                            · linarith only [h2887, h3218, hlam]
                                                            · linarith only [h2872, h3218, hlam]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [hlam, p3198_0]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h2314, h2873, h2889, h3109, h3123, hc23, hc34, hlam, hphi, p3198_1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h2314, h2315, h3109, hc23, hc45, hlam, hphi, ht34, p3198_1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h3116, hlam, p3198_1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h3110, h3116, h3121, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3198_1, u2elo1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [h3123, hlam, p3198_1]
                                                          · have p3198_0 := h3198c.1
                                                            have p3198_1 := h3198c.2.1
                                                            have p3198_2 := h3198c.2.2.1
                                                            have p3198_3 := h3198c.2.2.2
                                                            linarith only [hlam, p3198_0]
                                                        · linarith only [h3197, hlam, p3155_0]
                                                      · linarith only [h2873, h3196, hlam]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                rcases p3155_3 (m.d 0 3) (by simp) with h3230 | h3230
                                                · linarith only [h2887, h3230, hlam]
                                                · linarith only [h2314, h3230, hlam]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                rcases p3155_3 (m.d 0 3) (by simp) with h3233 | h3233
                                                · linarith only [h2887, h3233, hlam]
                                                · linarith only [h2870, h3233, hlam]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [h3123, hlam, p3155_1]
                                              · have p3155_0 := h3155c.1
                                                have p3155_1 := h3155c.2.1
                                                have p3155_2 := h3155c.2.2.1
                                                have p3155_3 := h3155c.2.2.2
                                                linarith only [hlam, p3155_0]
                                      · linarith only [h3111, h3148, hlam]
                                    · linarith only [h3147, hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3124_1, u2elo1]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    rcases p3124_3 (m.d 0 2) (by simp) with h3242 | h3242
                                    · linarith only [h0, h3242, hlam]
                                    · linarith only [h2870, h3242, hlam]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    rcases p3124_3 (m.d 0 2) (by simp) with h3245 | h3245
                                    · linarith only [h0, h3245, hlam]
                                    · linarith only [h2871, h3245, hlam]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    rcases p3124_3 (m.d 0 2) (by simp) with h3248 | h3248
                                    · linarith only [h0, h3248, hlam]
                                    · linarith only [h2872, h3248, hlam]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h2870, hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h3109, hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h3117, hlam, p3124_1]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h3119, hlam, p3124_1]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h2871, hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h3110, hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h2871, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3124_1, u2elo0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h3121, hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h2872, hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h3111, hlam, p3124_0]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h2872, h2889, h3110, h3116, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3124_1, u2elo1]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [h2872, h2889, h3110, h3116, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3124_1, u2elo1]
                                  · have p3124_0 := h3124c.1
                                    have p3124_1 := h3124c.2.1
                                    have p3124_2 := h3124c.2.2.1
                                    have p3124_3 := h3124c.2.2.2
                                    linarith only [hlam, p3124_0]
                                · linarith only [h2314, h2873, h3109, h3110, h3116, h3123, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3267 | h3267
                          · linarith only [h2314, h2315, h2873, h3109, h3116, h3267, hc04, hc45, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3269 | h3269
                            · linarith only [h2314, h2315, h3109, h3111, h3269, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3271 | h3271
                              · linarith only [h2871, h2889, h3271, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3273 | h3273
                                · linarith only [h2314, h2315, h3109, h3116, h3273, hc23, hc34, hlam, hphi]
                                · rcases h2bigk with h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c | h3275c
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h0, hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    rcases p3275_3 (m.d 0 2) (by simp) with h3278 | h3278
                                    · rcases p3275_3 (m.d 1 2) (by simp) with h3279 | h3279
                                      · rcases p3275_3 (m.d 2 3) (by simp) with h3280 | h3280
                                        · linarith only [h3280, hlam, p3275_0]
                                        · rcases p3275_3 (m.d 2 4) (by simp) with h3282 | h3282
                                          · linarith only [h2871, h3282, hlam]
                                          · linarith only [h3267, h3282, hlam]
                                      · linarith only [h3109, h3279, hlam]
                                    · linarith only [h3278, hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    rcases p3275_3 (m.d 0 2) (by simp) with h3287 | h3287
                                    · rcases p3275_3 (m.d 1 2) (by simp) with h3288 | h3288
                                      · rcases p3275_3 (m.d 2 3) (by simp) with h3289 | h3289
                                        · linarith only [h2870, h3289, hlam]
                                        · rcases p3275_3 (m.d 2 4) (by simp) with h3291 | h3291
                                          · linarith only [h3291, hlam, p3275_0]
                                          · rcases p3275_3 (m.d 2 5) (by simp) with h3293 | h3293
                                            · linarith only [h2872, h3293, hlam]
                                            · linarith only [h3271, h3293, hlam]
                                      · linarith only [h3110, h3288, hlam]
                                    · linarith only [h3287, hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    rcases p3275_3 (m.d 0 2) (by simp) with h3298 | h3298
                                    · rcases p3275_3 (m.d 1 2) (by simp) with h3299 | h3299
                                      · rcases p3275_3 (m.d 2 3) (by simp) with h3300 | h3300
                                        · linarith only [h2870, h3300, hlam]
                                        · rcases p3275_3 (m.d 2 4) (by simp) with h3302 | h3302
                                          · linarith only [h2871, h3302, hlam]
                                          · rcases p3275_3 (m.d 2 5) (by simp) with h3304 | h3304
                                            · linarith only [h3304, hlam, p3275_0]
                                            · rcases h3bigk with h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c | h3306c
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h2314, h2315, h3111, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3306_1, u2elo1]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h2314, h2315, h3111, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3306_1, u2elo1]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h2873, hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h2887, hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h2314, hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h2314, h2315, h3111, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3306_1, u2elo1]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h3112, hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h3114, hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h2870, hlam, p3306_1]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h3109, hlam, p3306_1]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h3267, hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h3269, hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h3273, hc03, hc45, hlam, hphi, ht34, p3306_1]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h3109, h3273, hc23, hc45, hlam, hphi, ht34, p3306_1]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h3273, hc23, hc45, hlam, hphi, ht34, p3306_1]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h3273, hlam, p3306_0]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                rcases p3306_3 (m.d 0 3) (by simp) with h3327 | h3327
                                                · linarith only [h3327, hlam, p3306_0]
                                                · rcases p3306_3 (m.d 1 3) (by simp) with h3329 | h3329
                                                  · linarith only [h3114, h3329, hlam]
                                                  · rcases p3306_3 (m.d 2 3) (by simp) with h3331 | h3331
                                                    · linarith only [h3269, h3331, hlam]
                                                    · rcases p3306_3 (m.d 3 4) (by simp) with h3333 | h3333
                                                      · linarith only [h3273, h3333, hlam]
                                                      · linarith only [h2873, h3333, hlam]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                rcases p3306_3 (m.d 0 3) (by simp) with h3336 | h3336
                                                · linarith only [h2887, h3336, hlam]
                                                · linarith only [h2314, h3336, hlam]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                rcases p3306_3 (m.d 0 3) (by simp) with h3339 | h3339
                                                · linarith only [h2887, h3339, hlam]
                                                · linarith only [h2870, h3339, hlam]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [h2314, h2873, h3109, hc23, hc35, hlam, hphi, p3306_1]
                                              · have p3306_0 := h3306c.1
                                                have p3306_1 := h3306c.2.1
                                                have p3306_2 := h3306c.2.2.1
                                                have p3306_3 := h3306c.2.2.2
                                                linarith only [hlam, p3306_0]
                                      · linarith only [h3111, h3299, hlam]
                                    · linarith only [h3298, hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3275_1, u2elo1]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    rcases p3275_3 (m.d 0 2) (by simp) with h3348 | h3348
                                    · linarith only [h0, h3348, hlam]
                                    · linarith only [h2870, h3348, hlam]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    rcases p3275_3 (m.d 0 2) (by simp) with h3351 | h3351
                                    · linarith only [h0, h3351, hlam]
                                    · linarith only [h2871, h3351, hlam]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    rcases p3275_3 (m.d 0 2) (by simp) with h3354 | h3354
                                    · linarith only [h0, h3354, hlam]
                                    · linarith only [h2872, h3354, hlam]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h2870, hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h3109, hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h3267, hlam, p3275_1]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h3269, hlam, p3275_1]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h2871, hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h3110, hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h2871, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3275_1, u2elo0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h3271, hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h2872, hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h3111, hlam, p3275_0]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h0, h2872, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3275_1, u2elo1]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [h0, h2872, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3275_1, u2elo1]
                                  · have p3275_0 := h3275c.1
                                    have p3275_1 := h3275c.2.1
                                    have p3275_2 := h3275c.2.2.1
                                    have p3275_3 := h3275c.2.2.2
                                    linarith only [hlam, p3275_0]
                  · linarith only [h0, h2872, h3111, hlam]
                · linarith only [h0, h2314, h3109, h3110, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h3109, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3375 | h3375
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3376 | h3376
          · linarith only [h0, h2314, h2872, h3376, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3378 | h3378
            · linarith only [h2871, h2872, h3378, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3380 | h3380
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3381 | h3381
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3382 | h3382
                  · linarith only [h0, h2872, h3382, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2314, h3380, h3382, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h2314, h2871, h3380, h3381, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h3380, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3387 | h3387
          · linarith only [h2314, h2315, h3387, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3389 | h3389
            · linarith only [h2871, h2872, h3389, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3391 | h3391
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3392 | h3392
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3393 | h3393
                  · linarith only [h2872, h3393, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2314, h3391, h3393, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h2314, h3391, h3392, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2314, h3391, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3398 | h3398
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3399 | h3399
        · linarith only [h0, h2314, h2871, h3399, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3401 | h3401
          · linarith only [h2314, h2315, h3401, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3403 | h3403
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3404 | h3404
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3405 | h3405
                · linarith only [h2314, h2315, h2871, h3398, h3404, h3405, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h2314, h3404, h3405, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h3404, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h2871, h3398, h3403, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3410 | h3410
        · linarith only [h0, h2314, h2871, h3410, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3412 | h3412
          · linarith only [h0, h2314, h3398, h3412, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3414 | h3414
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3415 | h3415
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3416 | h3416
                · linarith only [h0, h2871, h3416, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2314, h3415, h3416, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h3415, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3420 | h3420
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3421 | h3421
                · linarith only [h0, h2314, h2871, h3420, h3421, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h2314, h3420, h3421, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2314, h3420, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
  · linarith only [h0, h2314, h2870, hlam]

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2314 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2315 | h2315
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x1_x0_x0 m hb2 hb3 hb5 h0 h2314 h2315
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x1_x0_x1 m hb2 hb3 hb5 h0 h2314 h2315

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3426 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3427 | h3427
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3428 | h3428
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
                                · linarith only [h3427, h3439, h3442, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · linarith only [h0, h3426, h3438, h3442, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h2314, h3426, h3433, h3438, h3441, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h2314, h3426, h3433, h3437, h3440, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3447 | h3447
                            · linarith only [h0, h3427, h3430, h3439, h3447, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h2314, h3426, h3433, h3437, h3447, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3450 | h3450
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3451 | h3451
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3452 | h3452
                              · linarith only [h3434, h3438, h3452, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3454 | h3454
                                · linarith only [h3438, h3450, h3454, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                                · rcases h2bigk with h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c | h3456c
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h0, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h0, h3450, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3456_1, u2elo1]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    rcases p3456_3 (m.d 0 2) (by simp) with h3460 | h3460
                                    · rcases p3456_3 (m.d 1 2) (by simp) with h3461 | h3461
                                      · rcases p3456_3 (m.d 2 3) (by simp) with h3462 | h3462
                                        · linarith only [h3427, h3462, hlam]
                                        · linarith only [h3450, h3462, hlam]
                                      · linarith only [h3434, h3461, hlam]
                                    · linarith only [h3460, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    rcases p3456_3 (m.d 0 2) (by simp) with h3467 | h3467
                                    · rcases p3456_3 (m.d 1 2) (by simp) with h3468 | h3468
                                      · rcases p3456_3 (m.d 2 3) (by simp) with h3469 | h3469
                                        · linarith only [h3427, h3469, hlam]
                                        · linarith only [h3451, h3469, hlam]
                                      · linarith only [h3435, h3468, hlam]
                                    · linarith only [h3467, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3456_1, u2elo1]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h3451, h3454, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3456_1, u2elo1]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    rcases p3456_3 (m.d 0 2) (by simp) with h3477 | h3477
                                    · linarith only [h0, h3477, hlam]
                                    · linarith only [h3428, h3477, hlam]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    rcases p3456_3 (m.d 0 2) (by simp) with h3480 | h3480
                                    · linarith only [h0, h3480, hlam]
                                    · linarith only [h3429, h3480, hlam]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h3427, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h3433, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h3427, h3450, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3456_1, u2elo0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h0, h3427, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3456_1, u2elo1]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h3428, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h3434, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h3450, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h3452, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h3429, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h3435, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h3451, hlam, p3456_0]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [h0, h3429, h3450, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3456_1, u2elo1]
                                  · have p3456_0 := h3456c.1
                                    have p3456_1 := h3456c.2.1
                                    have p3456_2 := h3456c.2.2.1
                                    have p3456_3 := h3456c.2.2.2
                                    linarith only [hlam, p3456_0]
                            · linarith only [h2314, h3426, h3433, h3437, h3451, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h2314, h3430, h3432, h3433, h3436, h3438, h3450, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h2314, h3431, h3437, hlam]
                    · linarith only [h2314, h3430, h3436, hlam]
                  · linarith only [h2314, h3433, h3435, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h2314, h3426, h3433, h3434, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
              · linarith only [h0, h3426, h3433, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3505 | h3505
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3506 | h3506
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3507 | h3507
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3508 | h3508
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3509 | h3509
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3510 | h3510
                        · linarith only [h0, h3426, h3428, h3432, h3510, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3512 | h3512
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3513 | h3513
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3514 | h3514
                              · linarith only [h3428, h3432, h3514, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3516 | h3516
                                · linarith only [h0, h3427, h3430, h3432, h3516, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases h2bigk with h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c | h3518c
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h0, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h0, h3512, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3518_1, u2elo1]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    rcases p3518_3 (m.d 0 2) (by simp) with h3522 | h3522
                                    · rcases p3518_3 (m.d 1 2) (by simp) with h3523 | h3523
                                      · rcases p3518_3 (m.d 2 3) (by simp) with h3524 | h3524
                                        · linarith only [h3427, h3524, hlam]
                                        · linarith only [h3512, h3524, hlam]
                                      · linarith only [h3506, h3523, hlam]
                                    · linarith only [h3522, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    rcases p3518_3 (m.d 0 2) (by simp) with h3529 | h3529
                                    · rcases p3518_3 (m.d 1 2) (by simp) with h3530 | h3530
                                      · rcases p3518_3 (m.d 2 3) (by simp) with h3531 | h3531
                                        · linarith only [h3427, h3531, hlam]
                                        · linarith only [h3513, h3531, hlam]
                                      · linarith only [h3507, h3530, hlam]
                                    · linarith only [h3529, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3518_1, u2elo1]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h3513, h3516, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3518_1, u2elo1]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    rcases p3518_3 (m.d 0 2) (by simp) with h3539 | h3539
                                    · linarith only [h0, h3539, hlam]
                                    · linarith only [h3428, h3539, hlam]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    rcases p3518_3 (m.d 0 2) (by simp) with h3542 | h3542
                                    · linarith only [h0, h3542, hlam]
                                    · linarith only [h3429, h3542, hlam]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h3427, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h3505, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h3427, h3512, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3518_1, u2elo0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h0, h3427, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3518_1, u2elo1]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h3428, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h3506, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h3512, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h3514, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h3429, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h3507, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h3513, hlam, p3518_0]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [h0, h3429, h3512, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3518_1, u2elo1]
                                  · have p3518_0 := h3518c.1
                                    have p3518_1 := h3518c.2.1
                                    have p3518_2 := h3518c.2.2.1
                                    have p3518_3 := h3518c.2.2.2
                                    linarith only [hlam, p3518_0]
                            · linarith only [h2314, h3426, h3505, h3509, h3513, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h2314, h3426, h3505, h3508, h3510, h3512, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h2314, h3431, h3509, hlam]
                    · linarith only [h2314, h3430, h3508, hlam]
                  · linarith only [h2314, h3426, h3505, h3507, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                · linarith only [h2314, h3426, h3505, h3506, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
              · linarith only [h0, h3426, h3505, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
          · linarith only [h2314, h3426, h3431, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3568 | h3568
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3569 | h3569
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3570 | h3570
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3571 | h3571
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3572 | h3572
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3573 | h3573
                    · linarith only [h2314, h3426, h3430, h3570, h3572, h3573, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3575 | h3575
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3576 | h3576
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3577 | h3577
                          · linarith only [h2314, h3426, h3572, h3573, h3577, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3579 | h3579
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3580 | h3580
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3581 | h3581
                                · rcases h2bigk with h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h0, hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h0, h3579, h3581, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3582_1, u2elo1]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h0, h3577, h3579, h3581, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3582_1, u2elo1]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    rcases p3582_3 (m.d 0 2) (by simp) with h3587 | h3587
                                    · rcases p3582_3 (m.d 1 2) (by simp) with h3588 | h3588
                                      · rcases p3582_3 (m.d 2 3) (by simp) with h3589 | h3589
                                        · linarith only [h3427, h3589, hlam]
                                        · linarith only [h3579, h3589, hlam]
                                      · linarith only [h3572, h3588, hlam]
                                    · linarith only [h3587, hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [hc02, hlam, hphi, p3582_1, u2elo1]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3579, h3581, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3582_1, u2elo1]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3577, h3579, h3581, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3582_1, u2elo1]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    rcases p3582_3 (m.d 0 2) (by simp) with h3598 | h3598
                                    · linarith only [h0, h3598, hlam]
                                    · linarith only [h3429, h3598, hlam]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3427, hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3570, hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3577, hlam, p3582_1]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3428, h3577, h3579, h3581, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3582_1, u2elo0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3428, hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3571, hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h0, h2314, h3426, h3428, h3572, h3573, h3579, h3581, hc23, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3582_1, u2elo1]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h0, h3428, h3579, h3581, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3582_1, u2elo1]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3429, hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3572, hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3579, hlam, p3582_0]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [h3580, hlam, p3582_1]
                                  · have p3582_0 := h3582c.1
                                    have p3582_1 := h3582c.2.1
                                    have p3582_2 := h3582c.2.2.1
                                    have p3582_3 := h3582c.2.2.2
                                    linarith only [hlam, p3582_0]
                                · linarith only [h2314, h3426, h3572, h3573, h3579, h3581, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                              · linarith only [h2314, h3426, h3573, h3576, h3580, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h2314, h3568, h3573, h3579, hc23, hc34, hlam, hphi]
                        · linarith only [h2314, h3426, h3569, h3573, h3576, hc04, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h2314, h3426, h3568, h3572, h3575, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h3572, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h2314, h3426, h3570, h3571, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
              · linarith only [h0, h3426, h3570, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h2314, h3426, h3430, h3569, hlam]
          · linarith only [h2314, h3426, h3568, hlam]
      · linarith only [h2314, h3426, h3427, h3429, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3627 | h3627
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3628 | h3628
        · linarith only [h3427, h3428, h3628, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3630 | h3630
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3631 | h3631
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3632 | h3632
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3633 | h3633
                · linarith only [h2314, h3427, h3428, h3633, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h3633, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h3426, h3427, h3632, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h3426, h3428, h3631, hlam]
          · linarith only [h2314, h3426, h3630, hlam]
      · linarith only [h2314, h3426, h3427, h3627, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3640 | h3640
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3641 | h3641
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3642 | h3642
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3643 | h3643
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3644 | h3644
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3645 | h3645
              · linarith only [h0, h3427, h3645, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h3426, h3645, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3648 | h3648
              · linarith only [h3427, h3640, h3648, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h0, h3426, h3648, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
          · linarith only [h0, h3426, h3427, h3643, hlam]
        · linarith only [h3427, h3640, h3642, hlam]
      · linarith only [h0, h3426, h3641, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3654 | h3654
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3655 | h3655
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3656 | h3656
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3657 | h3657
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3658 | h3658
              · linarith only [h0, h3427, h3658, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h3426, h3658, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h0, h3426, h3640, h3657, hlam]
          · linarith only [h0, h3426, h3640, h3655, h3656, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3663 | h3663
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3664 | h3664
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3665 | h3665
              · linarith only [h0, h3426, h3427, h3665, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h0, h3426, h3665, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h2314, h3426, h3655, h3664, hlam]
          · linarith only [h0, h3426, h3427, h3663, hlam]
      · linarith only [h0, h3426, h3654, hlam]

end R2N4
