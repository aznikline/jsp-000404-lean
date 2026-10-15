import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7126000 in
set_option maxHeartbeats 7126000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_23_L_R_L_I_H_I_s2 m hb0 hb2 hb3 h0 h1 h2
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2862 | h2862
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2863 | h2863
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2864 | h2864
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2865 | h2865
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2866 | h2866
            · linarith only [h0, h2, h2866, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2868 | h2868
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2869 | h2869
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2870 | h2870
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2871 | h2871
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2872 | h2872
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2873 | h2873
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2874 | h2874
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2875 | h2875
                            · rcases h2bigk with h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2868, h2872, h2875, hc02, hc45, hlam, hphi, ht0b, ht5b, p2876_1]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2, hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2, h2872, h2875, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2876_1]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                rcases p2876_3 (m.d 0 2) (by simp) with h2881 | h2881
                                · rcases p2876_3 (m.d 1 2) (by simp) with h2882 | h2882
                                  · linarith only [h0, h2882, hlam]
                                  · linarith only [h2869, h2882, hlam]
                                · linarith only [h2881, hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h0, hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2866, hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h0, h2872, h2875, hc01, hc45, hlam, hphi, ht0b, ht5b, p2876_1]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                rcases p2876_3 (m.d 0 2) (by simp) with h2890 | h2890
                                · rcases p2876_3 (m.d 1 2) (by simp) with h2891 | h2891
                                  · rcases p2876_3 (m.d 2 3) (by simp) with h2892 | h2892
                                    · rcases p2876_3 (m.d 2 4) (by simp) with h2893 | h2893
                                      · linarith only [h2868, h2893, hlam]
                                      · linarith only [h2874, h2893, hlam]
                                    · linarith only [h2873, h2892, hlam]
                                  · linarith only [h2891, hlam, p2876_0]
                                · linarith only [h2863, h2890, hlam]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p2876_1, u0ehi1]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2868, h2872, h2875, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2876_1]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                rcases p2876_3 (m.d 0 2) (by simp) with h2902 | h2902
                                · linarith only [h2, h2902, hlam]
                                · linarith only [h2862, h2902, hlam]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                rcases p2876_3 (m.d 0 2) (by simp) with h2905 | h2905
                                · linarith only [h2, h2905, hlam]
                                · linarith only [h2863, h2905, hlam]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2862, hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2868, hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2872, hlam, p2876_1]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h0, h2868, hc01, hc25, hlam, hphi, ht0b, ht5b, p2876_1]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2863, hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2869, hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2873, hlam, p2876_1]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [h2874, hlam, p2876_0]
                              · have p2876_0 := h2876c.1
                                have p2876_1 := h2876c.2.1
                                have p2876_2 := h2876c.2.2.1
                                have p2876_3 := h2876c.2.2.2
                                linarith only [hlam, p2876_0]
                            · linarith only [h0, h2, h2868, h2874, h2875, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2919 | h2919
                            · linarith only [h1, h2870, h2874, h2919, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases h2bigk with h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c | h2921c
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2, hc12, hc23, hlam, hphi, p2921_1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                rcases p2921_3 (m.d 0 2) (by simp) with h2925 | h2925
                                · rcases p2921_3 (m.d 1 2) (by simp) with h2926 | h2926
                                  · linarith only [h0, h2926, hlam]
                                  · linarith only [h2868, h2926, hlam]
                                · linarith only [h2925, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                rcases p2921_3 (m.d 0 2) (by simp) with h2930 | h2930
                                · rcases p2921_3 (m.d 1 2) (by simp) with h2931 | h2931
                                  · linarith only [h0, h2931, hlam]
                                  · linarith only [h2869, h2931, hlam]
                                · linarith only [h2930, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h0, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2866, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                rcases p2921_3 (m.d 0 2) (by simp) with h2938 | h2938
                                · rcases p2921_3 (m.d 1 2) (by simp) with h2939 | h2939
                                  · rcases p2921_3 (m.d 2 3) (by simp) with h2940 | h2940
                                    · rcases p2921_3 (m.d 2 4) (by simp) with h2941 | h2941
                                      · linarith only [h2941, hlam, p2921_0]
                                      · rcases p2921_3 (m.d 2 5) (by simp) with h2943 | h2943
                                        · linarith only [h2869, h2943, hlam]
                                        · linarith only [h2874, h2943, hlam]
                                    · linarith only [h2872, h2940, hlam]
                                  · linarith only [h2939, hlam, p2921_0]
                                · linarith only [h2862, h2938, hlam]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                rcases p2921_3 (m.d 0 2) (by simp) with h2949 | h2949
                                · rcases p2921_3 (m.d 1 2) (by simp) with h2950 | h2950
                                  · rcases p2921_3 (m.d 2 3) (by simp) with h2951 | h2951
                                    · rcases p2921_3 (m.d 2 4) (by simp) with h2952 | h2952
                                      · linarith only [h2868, h2952, hlam]
                                      · rcases p2921_3 (m.d 2 5) (by simp) with h2954 | h2954
                                        · linarith only [h2954, hlam, p2921_0]
                                        · rcases h3bigk with h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c | h2956c
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h2, h2866, h2873, h2919, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2921_1, p2956_1]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h2, hlam, p2956_1]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            rcases p2956_3 (m.d 0 3) (by simp) with h2960 | h2960
                                            · rcases p2956_3 (m.d 1 3) (by simp) with h2961 | h2961
                                              · linarith only [h1, h2961, hlam]
                                              · linarith only [h2870, h2961, hlam]
                                            · linarith only [h2960, hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            rcases p2956_3 (m.d 0 3) (by simp) with h2965 | h2965
                                            · rcases p2956_3 (m.d 1 3) (by simp) with h2966 | h2966
                                              · linarith only [h1, h2966, hlam]
                                              · linarith only [h2871, h2966, hlam]
                                            · linarith only [h2965, hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h1, hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h2866, hlam, p2956_1]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2956_1]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h1, h2919, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2956_1]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [hc23, hlam, hphi, ht01, ht12, p2956_1, u0ehi2]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h2866, h2873, h2919, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2921_1, p2956_1]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            rcases p2956_3 (m.d 0 3) (by simp) with h2978 | h2978
                                            · linarith only [h2, h2978, hlam]
                                            · linarith only [h2864, h2978, hlam]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            rcases p2956_3 (m.d 0 3) (by simp) with h2981 | h2981
                                            · linarith only [h2, h2981, hlam]
                                            · linarith only [h2865, h2981, hlam]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h2864, hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h2870, hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h2872, hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h2919, hlam, p2956_1]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h2865, hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h2871, hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h2873, hlam, p2956_0]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [h0, h2873, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2921_1, p2956_1]
                                          · have p2956_0 := h2956c.1
                                            have p2956_1 := h2956c.2.1
                                            have p2956_2 := h2956c.2.2.1
                                            have p2956_3 := h2956c.2.2.2
                                            linarith only [hlam, p2956_0]
                                    · linarith only [h2873, h2951, hlam]
                                  · linarith only [h2950, hlam, p2921_0]
                                · linarith only [h2863, h2949, hlam]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p2921_1, u0ehi1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                rcases p2921_3 (m.d 0 2) (by simp) with h2998 | h2998
                                · linarith only [h2, h2998, hlam]
                                · linarith only [h0, h2998, hlam]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                rcases p2921_3 (m.d 0 2) (by simp) with h3002 | h3002
                                · linarith only [h2, h3002, hlam]
                                · linarith only [h2862, h3002, hlam]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                rcases p2921_3 (m.d 0 2) (by simp) with h3005 | h3005
                                · linarith only [h2, h3005, hlam]
                                · linarith only [h2863, h3005, hlam]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2862, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2868, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2872, hlam, p2921_1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2874, hlam, p2921_1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2863, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2869, hlam, p2921_0]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h2873, hlam, p2921_1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [h0, h2869, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2921_1]
                              · have p2921_0 := h2921c.1
                                have p2921_1 := h2921c.2.1
                                have p2921_2 := h2921c.2.2.1
                                have p2921_3 := h2921c.2.2.2
                                linarith only [hlam, p2921_0]
                        · linarith only [h2, h2873, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · linarith only [h2, h2862, h2872, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · linarith only [h2866, h2869, h2871, hlam]
                  · linarith only [h2866, h2868, h2870, hlam]
                · linarith only [h2, h2863, h2868, h2869, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h2, h2862, h2868, hc12, hc23, hlam, hphi]
          · linarith only [h2, h2863, h2865, hlam]
        · linarith only [h2, h2862, h2864, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3026 | h3026
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3027 | h3027
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3028 | h3028
            · linarith only [h0, h2, h3028, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3030 | h3030
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3031 | h3031
                · linarith only [h2862, h2863, h3031, hc12, hlam, hphi, ht01, u0ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3033 | h3033
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3034 | h3034
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3035 | h3035
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3036 | h3036
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3037 | h3037
                          · linarith only [h0, h2863, h3030, h3037, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3039 | h3039
                            · linarith only [h0, h2863, h3030, h3035, h3037, h3039, hlam]
                            · rcases h2bigk with h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c | h3041c
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [hlam, p3041_0]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h2863, h3037, hc12, hc45, hlam, hphi, ht23, ht34, p3041_1]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h2, hlam, p3041_0]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h2863, h3035, h3037, hc34, hc45, hlam, hphi, p3041_1]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h2863, hlam, p3041_0]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h0, hlam, p3041_0]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [hlam, p3041_0]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h3028, hlam, p3041_0]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h0, h2863, h3035, h3037, hc34, hc45, hlam, hphi, p3041_1]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h3031, hlam, p3041_0]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p3041_1, u0ehi1]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                rcases p3041_3 (m.d 0 2) (by simp) with h3053 | h3053
                                · linarith only [h2, h3053, hlam]
                                · linarith only [h0, h3053, hlam]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [hlam, p3041_0]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                rcases p3041_3 (m.d 0 2) (by simp) with h3057 | h3057
                                · linarith only [h2, h3057, hlam]
                                · linarith only [h2862, h3057, hlam]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h2862, h2863, hc23, hlam, hphi, ht01, ht12, p3041_1, u0ehi3]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h2862, hlam, p3041_0]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h3030, hlam, p3041_0]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h3035, hlam, p3041_1]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [hlam, p3041_0]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h3037, hlam, p3041_1]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h2862, h3037, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p3041_1, u0ehi3]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h3030, h3037, hc24, hc45, hlam, hphi, p3041_1]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [h3036, hlam, p3041_1]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                rcases p3041_3 (m.d 0 2) (by simp) with h3069 | h3069
                                · linarith only [h2863, h3069, hlam]
                                · linarith only [h2862, h3069, hlam]
                              · have p3041_0 := h3041c.1
                                have p3041_1 := h3041c.2.1
                                have p3041_2 := h3041c.2.2.1
                                have p3041_3 := h3041c.2.2.2
                                linarith only [hlam, p3041_0]
                        · linarith only [h1, h2, h2862, h3034, h3036, hc03, hlam, hphi, u0ehi3]
                      · linarith only [h2, h2862, h3035, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3075 | h3075
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3076 | h3076
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3077 | h3077
                          · linarith only [h2, h3027, h3028, h3030, h3034, h3077, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3079 | h3079
                            · linarith only [h2, h3027, h3028, h3030, h3034, h3075, h3077, h3079, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases h2bigk with h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [hlam, p3081_0]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h2863, h3030, h3075, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3081_1]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h2, hlam, p3081_0]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h2863, h3075, h3077, hc34, hc45, hlam, hphi, p3081_1]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h2863, hlam, p3081_0]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h0, hlam, p3081_0]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [hlam, p3081_0]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h3028, hlam, p3081_0]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h3027, h3028, h3034, h3075, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3081_1]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h3031, hlam, p3081_0]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p3081_1, u0ehi1]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                rcases p3081_3 (m.d 0 2) (by simp) with h3093 | h3093
                                · linarith only [h2, h3093, hlam]
                                · linarith only [h0, h3093, hlam]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [hlam, p3081_0]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h2, h3027, h3028, h3030, h3034, hlam, p3081_2]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h2862, h2863, hc23, hlam, hphi, ht01, ht12, p3081_1, u0ehi3]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h2862, hlam, p3081_0]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h3030, hlam, p3081_0]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h3075, hlam, p3081_1]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [hlam, p3081_0]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h3077, hlam, p3081_1]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h2862, h3077, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p3081_1, u0ehi3]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h3030, h3077, hc24, hc45, hlam, hphi, p3081_1]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [h3076, hlam, p3081_1]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                rcases p3081_3 (m.d 0 2) (by simp) with h3107 | h3107
                                · linarith only [h2863, h3107, hlam]
                                · linarith only [h2862, h3107, hlam]
                              · have p3081_0 := h3081c.1
                                have p3081_1 := h3081c.2.1
                                have p3081_2 := h3081c.2.2.1
                                have p3081_3 := h3081c.2.2.2
                                linarith only [hlam, p3081_0]
                        · linarith only [h2, h3027, h3076, hlam]
                      · linarith only [h2, h3027, h3028, h3030, h3034, h3075, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h3028, h3030, h3033, hlam]
              · linarith only [h2, h2862, h3030, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3115 | h3115
            · linarith only [h2, h2862, h3115, hc12, hlam, hphi, ht01, u0ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3117 | h3117
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3118 | h3118
                · linarith only [h0, h2863, h3118, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3120 | h3120
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3121 | h3121
                    · linarith only [h3027, h3121, hc13, hlam, hphi, ht01, u0ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3123 | h3123
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3124 | h3124
                        · linarith only [h2, h2862, h3027, h3124, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                        · linarith only [h2, h2862, h3124, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · linarith only [h2, h2862, h3123, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                  · linarith only [h3026, h3027, h3120, hc13, hc35, hlam, hphi]
              · linarith only [h2, h2862, h3117, hc12, hc23, hlam, hphi]
        · linarith only [h2, h2862, h3026, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3131 | h3131
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3132 | h3132
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3133 | h3133
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3134 | h3134
            · linarith only [h0, h2, h3134, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3136 | h3136
              · linarith only [h2862, h3131, h3136, hc12, hlam, hphi, ht01, u0ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3138 | h3138
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3139 | h3139
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3140 | h3140
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3141 | h3141
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3142 | h3142
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3143 | h3143
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3144 | h3144
                            · rcases h2bigk with h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c | h3145c
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h2862, h3141, hc12, hc23, hlam, hphi, p3145_1]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h2, hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h2862, hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                rcases p3145_3 (m.d 0 2) (by simp) with h3150 | h3150
                                · rcases p3145_3 (m.d 1 2) (by simp) with h3151 | h3151
                                  · linarith only [h0, h3151, hlam]
                                  · linarith only [h3138, h3151, hlam]
                                · linarith only [h3150, hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h0, hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h3134, hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h3136, hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                rcases p3145_3 (m.d 0 2) (by simp) with h3159 | h3159
                                · rcases p3145_3 (m.d 1 2) (by simp) with h3160 | h3160
                                  · rcases p3145_3 (m.d 2 3) (by simp) with h3161 | h3161
                                    · rcases p3145_3 (m.d 2 4) (by simp) with h3162 | h3162
                                      · rcases p3145_3 (m.d 2 5) (by simp) with h3163 | h3163
                                        · linarith only [h3163, hlam, p3145_0]
                                        · rcases h3bigk with h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c | h3165c
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3139, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3165_1]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h2, hlam, p3165_1]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h2, h3144, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3165_1]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            rcases p3165_3 (m.d 0 3) (by simp) with h3170 | h3170
                                            · rcases p3165_3 (m.d 1 3) (by simp) with h3171 | h3171
                                              · linarith only [h1, h3171, hlam]
                                              · linarith only [h3140, h3171, hlam]
                                            · linarith only [h3170, hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h1, hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3134, hlam, p3165_1]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3144, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p3165_1]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h1, h3144, hc01, hc45, hlam, hphi, ht0b, ht5b, p3165_1]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [hc23, hlam, hphi, ht01, ht12, p3165_1, u0ehi2]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3134, h3142, h3144, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3145_1, p3165_1]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3144, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3165_1]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            rcases p3165_3 (m.d 0 3) (by simp) with h3184 | h3184
                                            · linarith only [h2, h3184, hlam]
                                            · linarith only [h3133, h3184, hlam]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3132, hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3139, hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3141, hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3132, h3144, hc03, hc45, hlam, hphi, ht0b, ht5b, p3165_1]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3133, hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3140, hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3142, hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [h3144, hlam, p3165_0]
                                          · have p3165_0 := h3165c.1
                                            have p3165_1 := h3165c.2.1
                                            have p3165_2 := h3165c.2.2.1
                                            have p3165_3 := h3165c.2.2.2
                                            linarith only [hlam, p3165_0]
                                      · linarith only [h3143, h3162, hlam]
                                    · linarith only [h3142, h3161, hlam]
                                  · linarith only [h3160, hlam, p3145_0]
                                · linarith only [h3131, h3159, hlam]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p3145_1, u0ehi1]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                rcases p3145_3 (m.d 0 2) (by simp) with h3202 | h3202
                                · linarith only [h2, h3202, hlam]
                                · linarith only [h0, h3202, hlam]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h2862, h3131, hc23, hlam, hphi, ht01, ht12, p3145_1, u0ehi4]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                rcases p3145_3 (m.d 0 2) (by simp) with h3207 | h3207
                                · linarith only [h2, h3207, hlam]
                                · linarith only [h3131, h3207, hlam]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h3131, hc24, hlam, hphi, ht01, ht12, p3145_1, u0ehi4]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                rcases p3145_3 (m.d 0 2) (by simp) with h3211 | h3211
                                · linarith only [h2862, h3211, hlam]
                                · linarith only [h0, h3211, hlam]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h3141, hlam, p3145_1]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                rcases p3145_3 (m.d 0 2) (by simp) with h3216 | h3216
                                · linarith only [h2862, h3216, hlam]
                                · linarith only [h3131, h3216, hlam]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h3131, hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h3138, hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h3142, hlam, p3145_1]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [h3143, hlam, p3145_0]
                              · have p3145_0 := h3145c.1
                                have p3145_1 := h3145c.2.1
                                have p3145_2 := h3145c.2.2.1
                                have p3145_3 := h3145c.2.2.2
                                linarith only [hlam, p3145_0]
                            · rcases h2bigk with h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c | h3224c
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h3138, h3143, h3144, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3224_1]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h2, hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h2862, hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h2862, h3141, h3143, h3144, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3224_1]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h0, hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h3134, hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h3136, hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h0, h3143, h3144, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3224_1]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p3224_1, u0ehi1]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h3138, h3143, h3144, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3224_1]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h2862, hc23, hlam, hphi, ht01, ht12, p3224_1, u0ehi3]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                rcases p3224_3 (m.d 0 2) (by simp) with h3239 | h3239
                                · linarith only [h2, h3239, hlam]
                                · linarith only [h3131, h3239, hlam]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h0, h3138, h3143, h3144, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3224_1]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h3138, h3143, h3144, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3224_1]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h3141, hlam, p3224_1]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                rcases p3224_3 (m.d 0 2) (by simp) with h3246 | h3246
                                · linarith only [h2862, h3246, hlam]
                                · linarith only [h3131, h3246, hlam]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h3131, hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h3138, hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h3142, hlam, p3224_1]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [h3143, hlam, p3224_0]
                              · have p3224_0 := h3224c.1
                                have p3224_1 := h3224c.2.1
                                have p3224_2 := h3224c.2.2.1
                                have p3224_3 := h3224c.2.2.2
                                linarith only [hlam, p3224_0]
                          · linarith only [h2862, h3143, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                        · linarith only [h2, h3131, h3142, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                      · linarith only [h2, h3131, h3141, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                    · linarith only [h3136, h3138, h3139, h3140, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3258 | h3258
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3259 | h3259
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3260 | h3260
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3261 | h3261
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3262 | h3262
                            · rcases h2bigk with h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c | h3263c
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h2862, h3138, h3260, h3262, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3263_1]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h2, hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h2862, hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                rcases p3263_3 (m.d 0 2) (by simp) with h3268 | h3268
                                · rcases p3263_3 (m.d 1 2) (by simp) with h3269 | h3269
                                  · linarith only [h0, h3269, hlam]
                                  · linarith only [h3138, h3269, hlam]
                                · linarith only [h3268, hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h0, hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h3134, hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h3136, hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h3132, h3134, h3139, h3260, h3262, hc03, hc45, hlam, hphi, ht0b, ht5b, p3263_1]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p3263_1, u0ehi1]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                rcases p3263_3 (m.d 0 2) (by simp) with h3279 | h3279
                                · linarith only [h2, h3279, hlam]
                                · linarith only [h0, h3279, hlam]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h2862, h3131, hc23, hlam, hphi, ht01, ht12, p3263_1, u0ehi4]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h2, h3132, h3134, h3138, h3139, hlam, p3263_2]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h3131, hc24, hlam, hphi, ht01, ht12, p3263_1, u0ehi4]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                rcases p3263_3 (m.d 0 2) (by simp) with h3286 | h3286
                                · linarith only [h2862, h3286, hlam]
                                · linarith only [h0, h3286, hlam]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h3259, hlam, p3263_1]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                rcases p3263_3 (m.d 0 2) (by simp) with h3291 | h3291
                                · linarith only [h2862, h3291, hlam]
                                · linarith only [h3131, h3291, hlam]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h3131, hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h3138, hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h3260, hlam, p3263_1]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [h3261, hlam, p3263_0]
                              · have p3263_0 := h3263c.1
                                have p3263_1 := h3263c.2.1
                                have p3263_2 := h3263c.2.2.1
                                have p3263_3 := h3263c.2.2.2
                                linarith only [hlam, p3263_0]
                            · linarith only [h3134, h3139, h3261, h3262, hc12, hc24, hlam, hphi]
                          · linarith only [h2862, h3131, h3261, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                        · linarith only [h2, h3132, h3134, h3138, h3139, h3260, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h2, h3132, h3259, hlam]
                    · linarith only [h3134, h3138, h3258, hlam]
                · linarith only [h2, h3131, h3138, hc12, hc23, hlam, hphi]
          · linarith only [h2862, h3131, h3132, h3133, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3306 | h3306
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3307 | h3307
            · linarith only [h2, h3307, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3309 | h3309
              · linarith only [h0, h2862, h3309, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3311 | h3311
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3312 | h3312
                  · linarith only [h3132, h3312, hc13, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3314 | h3314
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3315 | h3315
                      · linarith only [h2, h3131, h3132, h3315, hc23, hlam, hphi, ht01, ht12, u0ehi4]
                      · linarith only [h2, h3131, h3315, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                    · linarith only [h3132, h3306, h3314, hc13, hc34, hlam, hphi]
                · linarith only [h2, h3131, h3311, hc12, hc23, hlam, hphi]
          · linarith only [h2, h3131, h3306, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3321 | h3321
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3322 | h3322
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3323 | h3323
            · linarith only [h0, h2, h3323, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3325 | h3325
              · linarith only [h2862, h3325, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3327 | h3327
                · linarith only [h0, h3131, h3327, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3329 | h3329
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3330 | h3330
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3331 | h3331
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3332 | h3332
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3333 | h3333
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3334 | h3334
                            · rcases h2bigk with h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c | h3335c
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h3131, h3331, h3333, hc12, hc23, hlam, hphi, p3335_1]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h2, hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h2862, hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h3131, hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h0, hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h3323, hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h3325, hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h3327, hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p3335_1, u0ehi1]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                rcases p3335_3 (m.d 0 2) (by simp) with h3347 | h3347
                                · linarith only [h2, h3347, hlam]
                                · linarith only [h0, h3347, hlam]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h2862, hc23, hlam, hphi, ht01, ht12, p3335_1, u0ehi1]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h3131, hc23, hlam, hphi, ht01, ht12, p3335_1, u0ehi1]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [hc24, hlam, hphi, ht01, ht12, p3335_1, u0ehi1]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                rcases p3335_3 (m.d 0 2) (by simp) with h3354 | h3354
                                · linarith only [h2862, h3354, hlam]
                                · linarith only [h0, h3354, hlam]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h3331, hlam, p3335_1]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h3131, h3331, hc23, hlam, hphi, ht01, ht12, p3335_1, u0ehi1]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [hc25, hlam, hphi, ht01, ht12, p3335_1, u0ehi1]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                rcases p3335_3 (m.d 0 2) (by simp) with h3361 | h3361
                                · linarith only [h3131, h3361, hlam]
                                · linarith only [h0, h3361, hlam]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h3332, hlam, p3335_1]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [h3333, hlam, p3335_0]
                              · have p3335_0 := h3335c.1
                                have p3335_1 := h3335c.2.1
                                have p3335_2 := h3335c.2.2.1
                                have p3335_3 := h3335c.2.2.2
                                linarith only [hlam, p3335_0]
                            · rcases h2bigk with h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h2, hc12, hc23, hlam, hphi, p3367_1]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h2, hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h2862, hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h3131, hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h0, hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h3323, hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h3325, hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h3327, hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p3367_1, u0ehi1]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                rcases p3367_3 (m.d 0 2) (by simp) with h3379 | h3379
                                · linarith only [h2, h3379, hlam]
                                · linarith only [h0, h3379, hlam]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h2862, hc23, hlam, hphi, ht01, ht12, p3367_1, u0ehi1]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h3131, hc23, hlam, hphi, ht01, ht12, p3367_1, u0ehi1]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [hc24, hlam, hphi, ht01, ht12, p3367_1, u0ehi1]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                rcases p3367_3 (m.d 0 2) (by simp) with h3386 | h3386
                                · linarith only [h2862, h3386, hlam]
                                · linarith only [h0, h3386, hlam]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h3331, hlam, p3367_1]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h3131, h3331, hc23, hlam, hphi, ht01, ht12, p3367_1, u0ehi1]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [hc25, hlam, hphi, ht01, ht12, p3367_1, u0ehi1]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                rcases p3367_3 (m.d 0 2) (by simp) with h3393 | h3393
                                · linarith only [h3131, h3393, hlam]
                                · linarith only [h0, h3393, hlam]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h3332, hlam, p3367_1]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [h3333, hlam, p3367_0]
                              · have p3367_0 := h3367c.1
                                have p3367_1 := h3367c.2.1
                                have p3367_2 := h3367c.2.2.1
                                have p3367_3 := h3367c.2.2.2
                                linarith only [hlam, p3367_0]
                          · linarith only [h2862, h3333, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                        · linarith only [h1, h2, h3330, h3332, hc03, hlam, hphi, u0ehi1]
                      · linarith only [h1, h2, h3329, h3331, hc01, hlam, hphi, u0ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3402 | h3402
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3403 | h3403
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3404 | h3404
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3405 | h3405
                            · linarith only [h2, h3322, h3329, h3330, h3405, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases h2bigk with h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c | h3407c
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3131, hc12, hc25, hlam, hphi, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h2, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h2862, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3131, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h0, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3323, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3325, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3327, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p3407_1, u0ehi1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                rcases p3407_3 (m.d 0 2) (by simp) with h3419 | h3419
                                · linarith only [h2, h3419, hlam]
                                · linarith only [h0, h3419, hlam]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3330, h3404, h3405, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3131, hc23, hlam, hphi, ht01, ht12, p3407_1, u0ehi1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hc24, hlam, hphi, ht01, ht12, p3407_1, u0ehi1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                rcases p3407_3 (m.d 0 2) (by simp) with h3426 | h3426
                                · linarith only [h2862, h3426, hlam]
                                · linarith only [h0, h3426, hlam]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3402, hlam, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3131, h3402, hc23, hlam, hphi, ht01, ht12, p3407_1, u0ehi1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hc25, hlam, hphi, ht01, ht12, p3407_1, u0ehi1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                rcases p3407_3 (m.d 0 2) (by simp) with h3433 | h3433
                                · linarith only [h3131, h3433, hlam]
                                · linarith only [h0, h3433, hlam]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3403, hlam, p3407_1]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [h3404, hlam, p3407_0]
                              · have p3407_0 := h3407c.1
                                have p3407_1 := h3407c.2.1
                                have p3407_2 := h3407c.2.2.1
                                have p3407_3 := h3407c.2.2.2
                                linarith only [hlam, p3407_0]
                          · linarith only [h2862, h3404, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                        · linarith only [h2, h3403, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · linarith only [h2, h3322, h3329, h3330, h3402, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3442 | h3442
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3443 | h3443
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3444 | h3444
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3445 | h3445
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3446 | h3446
                            · rcases h2bigk with h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h2, hc12, hc23, hlam, hphi, p3447_1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h2, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h2862, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3131, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h0, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3323, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3325, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3327, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p3447_1, u0ehi1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                rcases p3447_3 (m.d 0 2) (by simp) with h3459 | h3459
                                · linarith only [h2, h3459, hlam]
                                · linarith only [h0, h3459, hlam]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3131, h3445, hc23, hlam, hphi, ht01, ht12, p3447_1, u0ehi4]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3131, hc23, hlam, hphi, ht01, ht12, p3447_1, u0ehi1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hc24, hlam, hphi, ht01, ht12, p3447_1, u0ehi1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                rcases p3447_3 (m.d 0 2) (by simp) with h3466 | h3466
                                · linarith only [h2862, h3466, hlam]
                                · linarith only [h0, h3466, hlam]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3443, hlam, p3447_1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3131, h3443, hc23, hlam, hphi, ht01, ht12, p3447_1, u0ehi1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hc25, hlam, hphi, ht01, ht12, p3447_1, u0ehi1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                rcases p3447_3 (m.d 0 2) (by simp) with h3473 | h3473
                                · linarith only [h3131, h3473, hlam]
                                · linarith only [h0, h3473, hlam]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3444, hlam, p3447_1]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [h3445, hlam, p3447_0]
                              · have p3447_0 := h3447c.1
                                have p3447_1 := h3447c.2.1
                                have p3447_2 := h3447c.2.2.1
                                have p3447_3 := h3447c.2.2.2
                                linarith only [hlam, p3447_0]
                            · linarith only [h3329, h3442, h3443, h3445, h3446, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h2862, h3445, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                        · linarith only [h2, h3329, h3442, h3444, hc03, hc34, hlam, hphi]
                      · linarith only [h2, h3321, h3443, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3483 | h3483
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3484 | h3484
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3485 | h3485
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3486 | h3486
                            · rcases h2bigk with h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h3131, h3485, hc12, hc24, hlam, hphi, p3487_1]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h2, hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h2862, hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h3131, hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h0, hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h3323, hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h3325, hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h3327, hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p3487_1, u0ehi1]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                rcases p3487_3 (m.d 0 2) (by simp) with h3499 | h3499
                                · linarith only [h2, h3499, hlam]
                                · linarith only [h0, h3499, hlam]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h2862, hc23, hlam, hphi, ht01, ht12, p3487_1, u0ehi1]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h3131, hc23, hlam, hphi, ht01, ht12, p3487_1, u0ehi1]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [hc24, hlam, hphi, ht01, ht12, p3487_1, u0ehi1]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                rcases p3487_3 (m.d 0 2) (by simp) with h3506 | h3506
                                · linarith only [h2862, h3506, hlam]
                                · linarith only [h0, h3506, hlam]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h3483, hlam, p3487_1]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h3131, h3483, hc23, hlam, hphi, ht01, ht12, p3487_1, u0ehi1]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [hc25, hlam, hphi, ht01, ht12, p3487_1, u0ehi1]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                rcases p3487_3 (m.d 0 2) (by simp) with h3513 | h3513
                                · linarith only [h3131, h3513, hlam]
                                · linarith only [h0, h3513, hlam]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h3484, hlam, p3487_1]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [h3485, hlam, p3487_0]
                              · have p3487_0 := h3487c.1
                                have p3487_1 := h3487c.2.1
                                have p3487_2 := h3487c.2.2.1
                                have p3487_3 := h3487c.2.2.2
                                linarith only [hlam, p3487_0]
                            · linarith only [h3323, h3329, h3483, h3485, h3486, hc12, hc23, hlam, hphi]
                          · linarith only [h2862, h3485, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                        · linarith only [h2, h3322, h3484, hc03, hlam, hphi, u0ehi1]
                      · linarith only [h2, h3483, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3523 | h3523
            · linarith only [h2, h3523, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3525 | h3525
              · linarith only [h2862, h3525, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3527 | h3527
                · linarith only [h0, h3131, h3527, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3529 | h3529
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3530 | h3530
                    · linarith only [h1, h3322, h3530, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3532 | h3532
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3533 | h3533
                        · linarith only [h3322, h3533, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                        · linarith only [h2, h3533, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · linarith only [h1, h2, h3529, h3532, hc03, hlam, hphi, u0ehi1]
                  · linarith only [h3321, h3322, h3529, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3538 | h3538
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3539 | h3539
            · linarith only [h0, h2, h3539, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3541 | h3541
              · linarith only [h0, h2862, h3541, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3543 | h3543
                · linarith only [h0, h3131, h3543, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3545 | h3545
                  · linarith only [h3131, h3321, h3538, h3545, hc13, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3547 | h3547
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3548 | h3548
                      · linarith only [h3131, h3321, h3538, h3548, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                      · linarith only [h2, h3548, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h3321, h3538, h3547, hc13, hc34, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3552 | h3552
            · linarith only [h2, h3552, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3554 | h3554
              · linarith only [h2862, h3554, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3556 | h3556
                · linarith only [h0, h3131, h3556, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3558 | h3558
                  · linarith only [h1, h3321, h3558, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3560 | h3560
                    · linarith only [h1, h3538, h3560, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3562 | h3562
                      · linarith only [h3321, h3562, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                      · linarith only [h2, h3562, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

end R2N4
